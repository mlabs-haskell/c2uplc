{- HLINT ignore "Use if" -}
{-# LANGUAGE ViewPatterns #-}

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
import Covenant.Index (Count, Index)
import Data.Foldable (foldl')
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe)
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Optics.Core (preview, review)

newtype LambdaId = LambdaId {_getLamId :: Id}
    deriving newtype (Show, Eq, Ord)

newtype AppId = AppId {_getAppId :: Id}
    deriving newtype (Show, Eq, Ord)

{- This gives us every possible concretification of a rigid tyvar for a given App site.

   NOTE: This ONLY tells us about rigid instantiations. This is important to keep in mind,
         because we may have to perform transformations or generate "versions" of functions
         which are polymorphic but always immediately concretified by being applied to
         concrete types.
-}
getTyVarConcretifications ::
    ASG ->
    Map LambdaId (Set LambdaId) -> -- call chains
    Map LambdaId (Set AppId) -> -- call sites
    Map AppId (Vector LambdaId) -> -- call site chains
    AppId ->
    -- I think we have to return the "as concrete as possible" function type for each
    -- call site as well. We need it in the recursive calls. If we don't have it, we can determine
    -- THAT some type concretifies a rigid, but we can't say WHICH type that is
    (CompT AbstractTy, Set (Map AbstractTy (ValT Void)))
getTyVarConcretifications asg callChains callSites callSiteChains appId@(AppId i) = case nodeAt i asg of
    -- Am reasonably certain we never actually need to examine the explicit type applications/instantiations here
    AValNode _valT (App _fn _args _instTys fnTy) -> case decideConcreteCompT fnTy of
        {-
          1. Identify all rigids
          2. Resolve them
        -}
        Nothing ->
            let rigids = collectRigids fnTy
                -- Explanation: This is a [[Map AbstractTy (ValT Void)]].
                --              Each INNER list should be a collection of concrete singleton maps of instantiation types for a given rigid we collected from
                --              our "as-concrete-as-possible" function type. (The maps are a convenience here, this is "morally" a [[(AbstractTy,ValT Void)]] - note the singleton-ey-ness)
                --
                --              The order of the outer list doesn't really indicate anything at all, it's only for grouping.
                --
                --              Just to make this clearer, suppose that `tN@rM` means: 'tN is a concrete type that can concretify some rigid r identified by M'
                --              (this is a slight simplification).
                --              resolvedRigids should look like: [ [t0@r0, t1@r0, t2@r0], [t3@r1, t4@r1], [t5@r2]  ]
                --
                --              What we want out of this is something like "every possible union of all of those singleton maps such that every map has
                --              an entry for every rigid".
                resolvedRigids = resolveRigid <$> S.toList rigids
             in -- REVIEW: We need to tag the results with `fnTy` for recursive calls. I think? ugh
                (fnTy,) . S.fromList . combine $ resolvedRigids
        Just _ ->
            -- This has to be empty. If the application site is fully concretified, there are no rigids, and there's nothing we can do.
            (fnTy, S.empty)
    _ -> error "AppId not an app! BOOOOOM!"
  where
    -- "unsafe" way to retrieve the original (i.e. possibly polymorphic) lambda type
    lambdaTy :: LambdaId -> CompT AbstractTy
    lambdaTy (LambdaId l) = case nodeAt l asg of
        ACompNode compT _ -> compT
        _other -> error "Lambda id points at non-comp-node"

    -- There has to be a term for what this does (can't remember it), but the general idea is given by the example:
    -- `combine [["a","b"],["c"],["d","e"]]` ~ `["acd","ace","bcd","bce"]`
    combine :: forall (a :: Type). (Monoid a) => [[a]] -> [a]
    combine [] = []
    combine (xs : xss) = go xs xss
      where
        go :: [a] -> [[a]] -> [a]
        go as [] = as
        go as (ys : yss) =
            let as' = (<>) <$> as <*> ys
             in go as' yss
    -- This really collects every *type variable* in a CompT, but at this point, the only ones left really should be rigid.
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

    -- Checks whether a "was rigid" (identified by the Index) is instantiated at a given call site of the lambda
    -- which binds it, and if so, sorts the resulting type that instantiates it into concrete or abstract.
    concretifies ::
        Index "tyvar" -> -- The arg index of the rigid. We know the DeBruijn must be Z
        AppId -> -- AppId of *a* call site of a "parent" lambda that binds the rigid we're examining
        -- We either get:
        --   1. Nothing (which indicates an internal error or something weird with a phantom type variable
        --      (REVIEW: Do we sufficiently 'check' for phantom tyvars before this? The requirements here
        --               may differ from our previous ones. A phantom tyvar is fine if it's never *used*
        --               anywhere, but things could get really broken if we don't forbid their use
        --               ***in explicit type applications that would result in them being a ridid***.
        --      )
        --   2. An rigid type variable, which means we have more work to do.
        --   3. A concrete type, which is what we want.
        Wedge (ValT Void) (ValT AbstractTy)
    concretifies argPos (AppId pcsId) = case nodeAt pcsId asg of
        AValNode _ (App fn _args _instArgs monoFunTy) ->
            let polyFunTy = lambdaTy (LambdaId fn)
                var = BoundAt Z argPos
             in case instantiationHelper id var monoFunTy polyFunTy of
                    Nothing -> Nowhere
                    Just ty -> case decideConcrete ty of
                        Nothing -> There ty
                        Just ty' -> Here ty'
        _ -> error "App node does not point at an App ValNode!!!"

    -- This returns EVERY POSSIBLE INSTANTIATION FOR A GIVEN ARGPOS. Or it should anyway!
    -- NOTE: That means that this is "every possibility for a specific tyvar".
    resolveRigid :: AbstractTy -> [Map AbstractTy (ValT Void)]
    resolveRigid rigid@(BoundAt db argPos) = concatMap resolveHelper parentCallSites
      where
        -- 1. We need to find the ID of the lambda that corresponds to the DeBruijn index
        --    of our rigid (i.e. the lambda which binds that rigid)
        --    We *should* be able to get that by indexing into the entry of our
        --    call chain map for our AppId key using the DeBruijn. I think?
        --    NOTE: I'm doing unsafe indexing for convenience and to simply things, we might want to
        --          switch to safe indexing later w/ real errors
        parentLambdaId :: LambdaId
        parentLambdaId = (callSiteChains M.! appId) Vector.! review asInt db
        -- 2. Then we need to collect all of the call sites for that lambda. I think?
        parentCallSites :: Set AppId
        parentCallSites = callSites M.! parentLambdaId

        -- 3. This is where it get complicated.
        resolveHelper :: AppId -> [Map AbstractTy (ValT Void)]
        resolveHelper parentAppId = case concretifies argPos parentAppId of
            -- This happens when we can't determine the instantiation of a rigid at an application of the lambda that binds it.
            -- We can't meaningfully recover - it means that we *need* a rigid (because it appears in the signature of a function)
            -- but the rigid does not appear as a bound tyvar in the (applied/instantiated) function signature at a call site of its binding lambda.
            -- (or it means we really screwed something up here!)
            Nowhere ->
                error $
                    "Something went wrong when determining type variable concretifications. This could indicate either "
                        <> " an internal compiler error, or a misuse of phantom type variables in type applications of a dependent lambda"
            -- If it's not concrete then we have more chasing to do.
            -- We should be fine to call our top level function recursively here, though an unfortunate consequence of the
            -- way I've set this up is that the only easy way to do this has HORRIBLE complexity since we'll
            -- need to call the top level function a bunch of times. Whatever, optimize it later.
            There _abstractTy ->
                let
                    -- The original polymorphic function type of the lambda that binds the rigid we care about
                    parentPolyFunTy :: CompT AbstractTy
                    parentPolyFunTy = lambdaTy parentLambdaId
                    -- Every transitive concretifiction of this parent lambda (the recursive call to our top level function)
                    parentAbsFnTy :: CompT AbstractTy
                    parentConcretifications :: [Map AbstractTy (ValT Void)]
                    (parentAbsFnTy, parentConcretifications) = S.toList <$> getTyVarConcretifications asg callChains callSites callSiteChains parentAppId
                    -- The concretified function types with the rigids resolved for each call site. These SHOULD REALLY BE FULLY CONCRETE.
                    -- NOTE/REVIEW: I am not sure what to do if they are *not* fully concrete. We've kind of reached the end of the line here. There's nowhere else
                    --              we could look, afaict, to further concretify them.
                    fullyConcreteParentTypes :: [CompT AbstractTy]
                    fullyConcreteParentTypes = map (\instMap -> substCompT vacuous instMap parentAbsFnTy) parentConcretifications
                    -- We need to prove the types concrete, so we do so.
                    -- NOTE: We might want this to error on `Nothing`s so we know that something has gone wrong
                    --       (but I'll change that while debugging, maybe it'll just work... hahaha)
                    provenConcreteParentTypes :: [CompT Void]
                    provenConcreteParentTypes = mapMaybe decideConcreteCompT fullyConcreteParentTypes
                    -- This is the var "resolved" relative to the parent lambda's level. I am pretty sure it should always be a
                    -- `BoundAt Z ...`
                    var = BoundAt Z argPos
                    -- This is what we've been driving at: A list of every possible concretification of this rigid for each call site of the parent function
                    -- NOTE(to self): might want to throw errors on `Nothing` cases instead of using `mapMaybe`, at least for debugging
                    concretificationsForThisRigid :: [ValT Void]
                    concretificationsForThisRigid =
                        mapMaybe
                            ( \concrete ->
                                decideConcrete
                                    =<< instantiationHelper vacuous var concrete parentPolyFunTy
                            )
                            provenConcreteParentTypes
                 in
                    M.singleton rigid <$> concretificationsForThisRigid
            -- We already did the work in `concretifies`, we just return a singleton list of a singleton map w/ the instantiation
            Here concreteResult -> [M.singleton rigid concreteResult]

-- 'getInstantiations' but works on the types we actually need
instantiationHelper ::
    forall (a :: Type).
    (CompT a -> CompT AbstractTy) -> -- need to pass this in so we can use this on CompT Voids
    AbstractTy -> -- the tyvar
    CompT a -> -- The more concrete type. Might be CompT Void if we KNOW it's concrete
    CompT AbstractTy -> -- The more polymorphic type.
    Maybe (ValT AbstractTy)
instantiationHelper f var concrete poly = M.lookup var $ runReader (getInstantiations [var] poly' concrete') 0
  where
    concrete' = Vector.toList . compTArgSchema $ f concrete
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

substCompT ::
    forall (a :: Type).
    (ValT a -> ValT AbstractTy) ->
    Map AbstractTy (ValT a) ->
    CompT AbstractTy ->
    CompT AbstractTy
substCompT f dict (CompN cnt (compTBodyToVec -> bodyVec)) = CompN cnt (vecToCompTBody subbed) -- NOTE: COUNT WILL BE WRONG (I don't think it matters)
  where
    subbed = (\vt -> runReader (substitute f dict vt) 0) <$> bodyVec

-- the extra function arg lets this work with either AbstractTy or Void (which might be useful for us)
substitute ::
    forall (a :: Type).
    (ValT a -> ValT AbstractTy) ->
    Map AbstractTy (ValT a) ->
    ValT AbstractTy ->
    Reader Int (ValT AbstractTy)
substitute f dict = \case
    Abstraction a ->
        resolveVar a >>= \a' -> case M.lookup a' dict of
            Nothing -> pure $ Abstraction a
            Just t -> pure (f t)
    ThunkT (CompN cnt concreteFn) -> do
        let bodyAsVec = compTBodyToVec concreteFn
        subbedBody <- local (+ 1) $ traverse (substitute f dict) bodyAsVec
        pure . ThunkT . CompN cnt $ vecToCompTBody subbedBody
    Datatype tn args -> Datatype tn <$> traverse (substitute f dict) args
    other -> pure other
