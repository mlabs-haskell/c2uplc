{- HLINT ignore "Use if" -}
module Covenant.Concretify (
    getTyVarConcretifications,
    getAllNodes,
    getCallSiteChainMap,
    getCallChain,
    getLambdaSubASG,
    tyInstDeps,
    getCallSites,
    allLambdas,
) where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (ask, local)

import Covenant.ASG (
    ASG,
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
 )
import Covenant.Type (AbstractTy (BoundAt), CompT (CompN), CompTBody (ArgsAndResult, ReturnT), ValT (Abstraction, BuiltinFlat, Datatype, ThunkT))

import Control.Applicative (Alternative ((<|>)))
import Control.Monad.Reader (Reader, runReader)
import Covenant.DeBruijn (DeBruijn (Z), asInt)
import Covenant.Index (Count)
import Data.Foldable (foldl')
import Data.Maybe (fromJust)
import Data.Void (Void, vacuous)
import Optics.Core (preview, review)

newtype LambdaId = LambdaId {_getLamId :: Id}
    deriving newtype (Show, Eq, Ord)

newtype AppId = AppId {_getAppId :: Id}
    deriving newtype (Show, Eq, Ord)

{- This gives us every possible concretification of a rigid tyvar for a given App site.

   NOTE: This ONLY tells us about rigid instantiations. This is important to keep in mind,
         because we may have to perform transformations or generate "versions" of functions
         which never

-}
getTyVarConcretifications ::
    ASG ->
    Map LambdaId (Set LambdaId) -> -- call chains
    Map LambdaId (Set AppId) -> -- call sites
    Map AppId (Vector LambdaId) -> -- call site chains
    AppId ->
    Set (Vector (ValT Void))
getTyVarConcretifications asg callChains callSites callSiteChains appId@(AppId i) = case nodeAt i asg of
    -- Am reasonably certain we never actually need to examine the explicit type applications/instantiations here
    AValNode _valT (App _fn _args _instTys fnTy) -> case decideConcreteCompT fnTy of
        {-
          1. Identify all rigids
          2. Resolve them
        -}
        Nothing ->
            let rigids = collectRigids fnTy
                resolvedRigids = combine $ resolveRigid <$> S.toList rigids
             in S.fromList . fmap Vector.fromList $ resolvedRigids
        Just{} ->
            --
            undefined
    _ -> error "AppId not an app! BOOOOOM!"
  where
    combine :: forall a. [[a]] -> [[a]]
    combine = foldr go []
      where
        go :: [a] -> [[a]] -> [[a]]
        go curr acc = (:) <$> curr <*> acc

    collectRigids :: CompT AbstractTy -> Set AbstractTy
    collectRigids =
        mconcat
            . Vector.toList
            . fmap (flip runReader 0 . go)
            . compTArgSchema
      where
        go :: ValT AbstractTy -> Reader Int (Set AbstractTy)
        go = \case
            Abstraction x -> S.singleton <$> resolveVar x
            ThunkT compT -> local (+ 1) $ do
                let argSchema = compTArgSchema compT
                mconcat <$> traverse go (Vector.toList argSchema)
            BuiltinFlat{} -> pure S.empty
            Datatype _ args -> mconcat <$> traverse go (Vector.toList args)

    -- This returns EVERY POSSIBLE INSTANTIATION FOR A GIVEN ARGPOS. Or it should anyway!
    -- NOTE: That means that this is "every possibility for a specific tyvar".
    resolveRigid :: AbstractTy -> [ValT Void]
    resolveRigid (BoundAt db argPos) = concatMap resolveHelper parentCallSites
      where
        -- 1. We need to find the ID of the lambda that corresponds to the DeBruijn index
        --    of our rigid.
        --    We *should* be able to get that by indexing into the entry of our
        --    call chain map for our AppId key using the DeBruijn. I think?
        --    NOTE: I'm doing unsafe indexing for convenience and to simply things, we might want to
        --          switch to safe indexing later w/ real errors
        lambdaId = (callSiteChains M.! appId) Vector.! review asInt db
        -- 2. Then we need to collect all of the call sites for that lambda. I think?
        parentCallSites = S.toList $ callSites M.! lambdaId
        -- 3. This is where it get complicated. For each call site, there are two possibilities:
        --      a) It concretifies the variable we care about
        --      b) It doesn't do that, and we have more "chasing" to do
        --    This isn't conceptually complicated but it is tricky. We want to recurse using the top level function here
        --    but ONLY on those call sites which do not concretify *this* variable.
        resolveHelper :: AppId -> [ValT Void]
        resolveHelper parent@(AppId parentAppId) = case nodeAt parentAppId asg of
            AValNode _ (App fn _args _ concreteTy') -> case decideConcreteCompT concreteTy' of
                -- If it's not concrete then we have more chasing to do, pretty sure.
                -- We should be fine to call our top level function recursively here, though an unfortunate consequence of the
                -- way I've set this up is that the only easy way to do this has HORRIBLE complexity since we'll
                -- need to call the top level function a bunch of times. Whatever, optimize it later.
                Nothing ->
                    let parentVersions = S.toList $ getTyVarConcretifications asg callChains callSites callSiteChains parent
                     in (Vector.! 0) <$> parentVersions
                -- If the applied type is concrete in the parent, we need to determine what the tyvar we care about actually
                -- got instantiated to. There isn't a *trivial* way to do that, however, fortunately we know enough to determine this:
                -- The instantiation we're looking for will always be of the form `BoundAt Z argPos`
                -- We do, however, need to lookup the type of the raw polymorphic function however, since we can't figure out the
                -- instantiation without it.
                Just concreteTy ->
                    let var = BoundAt Z argPos
                        polyFunTy = case nodeAt fn asg of
                            ACompNode ty _ -> ty
                            _ -> error "BOOOOM lambdaId points at not-a-comp-node"
                     in case instantiationHelper var concreteTy polyFunTy of
                            Just aResult -> case decideConcrete aResult of
                                Nothing -> error "TODO: This really should be totally impossible. If we get this it means we swapped args around somewhere"
                                Just concreteResult -> [concreteResult]
                            Nothing -> error "TODO: Pretty sure this is also impossible! Only way we can get it is if we passed blatantly incorrect types to instantiationHelper"
            _ -> error "AppId not an app! BOOOOOM!"

-- 'getInstantiations' but works on the types we actually need
-- NOTE: This really shouldn't ever return Nothing if it's used in the above function, maybe fromJust it?
instantiationHelper :: AbstractTy -> CompT Void -> CompT AbstractTy -> Maybe (ValT AbstractTy)
instantiationHelper var concrete poly = M.lookup var $ runReader (getInstantiations [var] poly' concrete') 0
  where
    concrete' = Vector.toList . compTArgSchema $ vacuous concrete
    poly' = Vector.toList . compTArgSchema $ poly

-- Given a list of variables, one list of types representing the function type (minus the result, we don't care about it i think),
-- and a second list of types representing the arguments to which it is applied, determine all the instantiations
-- I know we hate lists but it seems really silly to do this w/ vectors...
getInstantiations :: [AbstractTy] -> [ValT AbstractTy] -> [ValT AbstractTy] -> Reader Int (Map AbstractTy (ValT AbstractTy))
getInstantiations [] _ _ = pure M.empty
getInstantiations _ [] _ = pure M.empty
getInstantiations _ _ [] = pure M.empty
getInstantiations (var : vars) fs@(fE : fEs) as@(aE : aEs) =
    instantiates var aE fE >>= \case
        Nothing -> (<>) <$> getInstantiations [var] fEs aEs <*> getInstantiations vars fs as
        Just t -> M.insert var t <$> getInstantiations vars fs as

instantiates ::
    AbstractTy ->
    ValT AbstractTy -> -- the "more concrete type", usually the actual argument from 'app'
    ValT AbstractTy -> -- the "more polymorphic type', usually from the fn definition
    Reader Int (Maybe (ValT AbstractTy))
instantiates var concrete abstract = case (concrete, abstract) of
    (x, Abstraction a) ->
        sameVar var a >>= \case
            True -> pure $ Just x
            False -> pure Nothing
    (ThunkT (CompN _ concreteFn), ThunkT (CompN _ abstractFn)) ->
        let concreteFn' = Vector.toList $ compTBodyToVec concreteFn
            abstractFn' = Vector.toList $ compTBodyToVec abstractFn
         in local (+ 1) $ go concreteFn' abstractFn'
    (Datatype tnC argsC, Datatype tnA argsA)
        | tnC == tnA -> go (Vector.toList argsC) (Vector.toList argsA)
    _ -> pure Nothing
  where
    -- second arg gets adjusted here, not first
    -- I THINK we need to do this?
    sameVar :: AbstractTy -> AbstractTy -> Reader Int Bool
    sameVar varA varB = do
        varB' <- resolveVar varB
        pure $ varA == varB'

    go :: [ValT AbstractTy] -> [ValT AbstractTy] -> Reader Int (Maybe (ValT AbstractTy))
    go [] _ = pure Nothing
    go _ [] = pure Nothing
    go (c : cs) (a : as) = (<|>) <$> instantiates var c a <*> go cs as

resolveVar :: AbstractTy -> Reader Int AbstractTy
resolveVar (BoundAt db ix) = do
    offset <- ask
    let db' = fromJust . preview asInt $ review asInt db - offset
    pure $ BoundAt db' ix

decideConcreteCompT :: CompT AbstractTy -> Maybe (CompT Void)
decideConcreteCompT (CompN cnt body) =
    fmap (compN cnt . vecToCompTBody) . traverse decideConcrete . compTBodyToVec $ body

decideConcrete :: ValT AbstractTy -> Maybe (ValT Void)
decideConcrete = \case
    Abstraction _ -> Nothing
    ThunkT (CompN cnt body) -> do
        body' <- traverse decideConcrete $ compTBodyToVec body
        pure . ThunkT . compN cnt $ vecToCompTBody body'
    BuiltinFlat biTy -> Just (BuiltinFlat biTy)
    Datatype tn args -> Datatype tn <$> traverse decideConcrete args

-- We need to collect all of the child ASGs for each lambda. We do this all in one pass, so the
-- second arg is still the top level id of the main ASG. The outer keys of the map are lambda node IDs and the
-- inner map is a representation of the ASG
getLambdaSubASG :: ASG -> Id -> Map LambdaId (Map Id ASGNode)
getLambdaSubASG asg i = case nodeAt i asg of
    AnError -> M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> case bRef of
            -- If the body is just an arg then I *think* there's nothing we can do here?
            AnArg{} -> M.empty
            AnId child ->
                let allChildNodes = getAllNodes asg child
                    here = M.singleton (LambdaId i) allChildNodes
                    smallerComponents = getLambdaSubASG asg child
                 in here <> smallerComponents
        Force fRef -> goRef fRef
        _ -> M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> M.empty
        -- We're going "top down" so we may not have encountered the lambda yet.
        -- This might lead to us processing the same lambda more than twice (which isn't great)
        -- but that shouldn't affect correctness and I can fix the performance later
        App fn args _ _ ->
            let fnAsg = getLambdaSubASG asg fn
                args' = Vector.foldMap goRef args
             in fnAsg <> args'
        Thunk child -> getLambdaSubASG asg child -- I think?
        Cata alg arg -> goRef alg <> goRef arg
        DataConstructor _tn _cn args -> Vector.foldMap goRef args
        Match scrut handlers -> goRef scrut <> Vector.foldMap goRef handlers
  where
    goRef :: Ref -> Map LambdaId (Map Id ASGNode)
    goRef = \case
        AnArg{} -> M.empty
        AnId ix -> getLambdaSubASG asg ix

getAllNodes :: ASG -> Id -> Map Id ASGNode
getAllNodes asg i = case thisNode of
    AnError -> here
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> here <> goRef bRef
        Force fRef -> here <> goRef fRef
        _ -> here
    AValNode _valT valNode -> case valNode of
        Lit _ -> here
        App fn args _ _ -> here <> getAllNodes asg fn <> Vector.foldMap goRef args
        Thunk child -> here <> getAllNodes asg child
        DataConstructor _tn _cn args -> here <> Vector.foldMap goRef args
        Match scrut handlers -> here <> goRef scrut <> Vector.foldMap goRef handlers
        Cata alg arg -> here <> goRef alg <> goRef arg
  where
    thisNode = nodeAt i asg
    here = M.singleton i thisNode

    goRef = \case
        AnArg{} -> M.empty
        AnId ix -> getAllNodes asg ix

getCallSiteChainMap :: ASG -> Id -> Map LambdaId (Set AppId) -> Reader (Vector LambdaId) (Map AppId (Vector LambdaId))
getCallSiteChainMap asg i callsites = case nodeAt i asg of
    AnError -> pure M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> case M.lookup (LambdaId i) callsites of
            Nothing -> goRef bRef
            Just{} -> local (Vector.cons (LambdaId i)) $ goRef bRef
        Force fRef -> goRef fRef
        _ -> pure M.empty
    AValNode _valT valNode -> case valNode of
        Lit{} -> pure M.empty
        App fn args _ _ -> case M.lookup (LambdaId fn) callsites of
            Nothing -> do
                fnPart <- getCallSiteChainMap asg fn callsites
                argsPart <- Vector.foldMap id <$> traverse goRef args
                pure $ fnPart <> argsPart
            Just{} -> do
                cxt <- ask
                M.insert (AppId i) cxt <$> do
                    fnPart <- getCallSiteChainMap asg fn callsites
                    argsPart <- Vector.foldMap id <$> traverse goRef args
                    pure $ fnPart <> argsPart
        Thunk child -> getCallSiteChainMap asg child callsites
        DataConstructor _ _ args -> Vector.foldMap id <$> traverse goRef args
        Match scrut handlers -> Vector.foldMap id <$> traverse goRef (scrut `Vector.cons` handlers)
        Cata alg arg -> Vector.foldMap id <$> traverse goRef (Vector.fromList [alg, arg])
  where
    goRef = \case
        AnArg{} -> pure M.empty
        AnId ix -> getCallSiteChainMap asg ix callsites

{- NOTE: I can probably rewrite this as a single traversal/fold after I know it works. Still kind of sick and
         doing it this way seemed likely to reduce the possibility for mistakes.
-}
getCallChain :: ASG -> Id -> Map LambdaId (Set LambdaId) -- it should be a NonEmpty but I just want to get the logic right for now
getCallChain asg i = foldl' go M.empty raw
  where
    -- Assumes that the top level is a function (it should be)
    raw :: Set (LambdaId, LambdaId)
    raw = runReader (getCallChain' asg i) (LambdaId i)

    go :: Map LambdaId (Set LambdaId) -> (LambdaId, LambdaId) -> Map LambdaId (Set LambdaId)
    go acc (caller, called) =
        M.alter
            ( \case
                Nothing -> Just $ S.singleton caller
                Just v -> Just $ S.insert caller v
            )
            called
            acc

getCallChain' :: ASG -> Id -> Reader LambdaId (Set (LambdaId, LambdaId)) -- (Container,Containee)
getCallChain' asg i = case nodeAt i asg of
    AnError -> pure S.empty
    ACompNode _compT compNode -> case compNode of
        Lam bRef -> do
            parent <- ask
            let here = (parent, LambdaId i)
            S.insert here <$> local (\_ -> LambdaId i) (goRef bRef)
        Force fRef -> goRef fRef
        _ -> pure S.empty
    AValNode _valT valNode -> case valNode of
        Lit{} -> pure S.empty
        App fn args _ _ -> do
            fnPart <- getCallChain' asg fn
            argsPart <- Vector.foldMap id <$> traverse goRef args
            pure $ fnPart <> argsPart
        Thunk child -> getCallChain' asg child
        DataConstructor _tn _cn args -> Vector.foldMap id <$> traverse goRef args
        Match scrut handlers -> do
            scrutPart <- goRef scrut
            handlersPart <- Vector.foldMap id <$> traverse goRef handlers
            pure $ scrutPart <> handlersPart
        Cata alg arg -> Vector.foldMap id <$> traverse goRef (Vector.fromList [alg, arg])
  where
    goRef = \case
        AnArg{} -> pure S.empty
        AnId ix -> getCallChain' asg ix

tyInstDeps :: ASG -> Id -> Reader (Vector Id) (Map Id (Map Id (Vector Id)))
tyInstDeps asg i = case nodeAt i asg of
    AnError -> pure M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bodyRef -> local (Vector.cons i) $ goRef bodyRef
        Force fRef -> goRef fRef
        _ -> pure M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> pure M.empty
        App fn args _ _ -> do
            cxt <- ask
            -- Our result is a Map LambdaId (Map AppId (Vector Id)), so the 'fn' comes first (somewhat unintuitively given the traversal order)
            let here = M.singleton fn (M.singleton i cxt)
            fnPart <- tyInstDeps asg fn
            argsParts <- M.unionsWith goMerge <$> traverse goRef (Vector.toList args)
            pure $ M.unionsWith goMerge [here, fnPart, argsParts]
        Thunk child -> tyInstDeps asg child
        Cata alg arg -> M.unionWith goMerge <$> goRef alg <*> goRef arg
        DataConstructor _tn _cn args -> M.unionsWith goMerge <$> (traverse goRef . Vector.toList $ args)
        Match scrut handlers -> do
            scrut' <- goRef scrut
            handlers' <- M.unionsWith goMerge <$> (traverse goRef . Vector.toList $ handlers)
            pure $ M.unionWith goMerge scrut' handlers'
  where
    goRef :: Ref -> Reader (Vector Id) (Map Id (Map Id (Vector Id)))
    goRef = \case
        AnId i' -> tyInstDeps asg i'
        AnArg{} -> pure M.empty

    -- I am not 10000% sure that (<>) is what we want so I'm splitting this out to a helper so it's easier to fix if I'm wrong.
    -- This does seem right though. We don't expect overlapping keys here.
    -- We still need to `unionWith/unionsWith` because the map monoid won't combine the monoids of its elements if they're monoidal
    goMerge :: Map Id (Vector Id) -> Map Id (Vector Id) -> Map Id (Vector Id)
    goMerge = (<>)

-- The Set Id in the return type is the set of all call sites of the lambda that is that key of that map entry
getCallSites :: Set Id -> ASG -> Id -> Map LambdaId (Set AppId)
getCallSites lambdas asg i = case nodeAt i asg of
    AnError -> M.empty
    ACompNode _compT compNode -> case compNode of
        Lam bodyRef -> goRef bodyRef
        Force fRef -> goRef fRef
        _ -> M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> M.empty
        App fn args _ _ -> case S.member fn lambdas of
            False -> M.unionWith (<>) (getCallSites lambdas asg fn) (Vector.foldMap goRef args)
            True ->
                let here = M.singleton (LambdaId fn) (S.singleton $ AppId i)
                    fromFn = getCallSites lambdas asg fn
                    fromArgs = M.unionsWith (<>) . map goRef . Vector.toList $ args
                 in M.unionsWith (<>) [here, fromFn, fromArgs]
        Thunk child -> getCallSites lambdas asg child
        Cata alg arg -> M.unionWith (<>) (goRef alg) (goRef arg)
        DataConstructor _tn _cn args -> M.unionsWith (<>) (goRef <$> args)
        Match scrut handlers -> M.unionWith (<>) (goRef scrut) (M.unionsWith (<>) (goRef <$> handlers))
  where
    goRef :: Ref -> Map LambdaId (Set AppId)
    goRef = \case
        AnId child -> getCallSites lambdas asg child
        AnArg _ -> M.empty

allLambdas :: ASG -> Id -> Set Id
allLambdas asg i = case nodeAt i asg of
    AnError -> mempty
    ACompNode _compT compNode -> case compNode of
        Lam bodyRef -> S.insert i $ goRef bodyRef
        Force fRef -> goRef fRef
        _aBuiltin -> mempty
    AValNode _valT valNode -> case valNode of
        Lit _ -> mempty
        App fn args _ _ ->
            let fnPart = allLambdas asg fn
                argsPart = Vector.foldMap goRef args
             in fnPart <> argsPart
        Thunk child -> allLambdas asg child
        Cata alg arg -> foldMap goRef [alg, arg]
        DataConstructor _tn _cn args -> Vector.foldMap goRef args
        Match scrut handlers -> goRef scrut <> Vector.foldMap goRef handlers
  where
    goRef :: Ref -> Set Id
    goRef = \case
        AnId child -> allLambdas asg child
        AnArg _ -> mempty

-- helpers

-- this is really fucking stupid but I don't have the time to do something better
compTBodyToVec :: forall a. CompTBody a -> Vector (ValT a)
compTBodyToVec (ArgsAndResult args res) = Vector.snoc args res

vecToCompTBody :: forall a. Vector (ValT a) -> CompTBody a
vecToCompTBody vec = case Vector.unsnoc vec of
    Just (args, res)
        | Vector.null args -> ReturnT res -- might not need this?
        | otherwise -> ArgsAndResult args res
    Nothing -> error "empty CompT"

compN :: Count "tyvar" -> CompTBody a -> CompT a
compN = error "Placeholder, we need to fix the pattern synonyms in the covenant repo b/c we can't construct a non-AbstractTy CompT -_-"

compTBody :: CompT a -> CompTBody a
compTBody = error "Placeholder, need a way to deconstruct a CompT that isn't a CompT AbstractTy"

compTArgSchema :: CompT a -> Vector (ValT a)
compTArgSchema t = case compTBody t of
    ArgsAndResult args _ -> args
