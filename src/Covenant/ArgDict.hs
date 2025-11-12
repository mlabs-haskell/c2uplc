{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Use <$>" -}
-- Seriously WTF this makes things so much uglier!
module Covenant.ArgDict (preprocess, idToName, compTVars) where

import Data.Word (Word64)

import Data.Kind (Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Text qualified as T

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, evalRWS, get, local, modify)

import Covenant.ASG (
    ASG,
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId,
 )
import Covenant.Type (AbstractTy (BoundAt), CompT (CompN), CompTBody (ArgsAndResult))

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (Index, intCount, intIndex)
import Data.Maybe (fromJust)
import Optics.Core (preview, review)
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

preprocess :: ASG -> Map Id (Either (Vector Name) (Vector Id))
preprocess asg = fst $ evalRWS (mkArgResolutionDict asg (topLevelId asg)) mempty (succ . fromEnum . topLevelId $ asg)

mkArgResolutionDict ::
    ASG ->
    Id -> -- needs to be the source node for top level calls of this fn
    RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id)))
mkArgResolutionDict asg i = case nodeAt i asg of
    AnError -> notALambda $ pure M.empty
    ACompNode compT compNode -> case compNode of
        Lam bodyRef -> do
            let numVarsBoundHere = compTArgs compT
                idW = idToWord i
            names <- Vector.fromList <$> traverse (lamArgName idW) [0 .. numVarsBoundHere]
            case bodyRef of
                AnId child -> local (Vector.cons i) $ do
                    res <- mkArgResolutionDict asg child
                    pure $ safeInsert i (Left names) res
                AnArg _ -> pure $ M.singleton i (Left names)
        Force fRef -> notALambda $ goRef fRef
        _someBuiltin -> notALambda $ pure M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> notALambda $ pure M.empty
        App fn args _ _ -> notALambda $ do
            fnDict <- mkArgResolutionDict asg fn
            argsDicts <- mconcat <$> traverse goRef (Vector.toList args)
            pure $ fnDict <> argsDicts
        Thunk child -> notALambda $ mkArgResolutionDict asg child
        Cata alg arg -> notALambda $ (<>) <$> goRef alg <*> goRef arg
        DataConstructor _tn _cn args -> notALambda $ mconcat <$> traverse goRef (Vector.toList args)
        Match scrut handlers -> notALambda $ mconcat <$> traverse goRef (scrut : Vector.toList handlers)
  where
    safeInsert :: forall (k :: Type) (v :: Type). (Ord k) => k -> v -> Map k v -> Map k v
    safeInsert k v = M.alter (\case Nothing -> Just v; other -> other) k

    lamArgName :: Word64 -> Int -> RWS (Vector Id) () Int Name
    lamArgName i' argPos = do
        let txtPart = "arg_" <> T.pack (show i') <> "_" <> T.pack (show argPos)
        uniquePart <- nextArgUnique
        pure $ Name txtPart (Unique uniquePart)

    nextArgUnique :: RWS (Vector Id) () Int Int
    nextArgUnique = do
        n <- get
        modify (+ 1)
        pure n

    goRef :: Ref -> RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id)))
    goRef = \case
        AnArg _ -> pure M.empty
        AnId anId -> mkArgResolutionDict asg anId

    notALambda ::
        RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id))) ->
        RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id)))
    notALambda act = do
        here <- Right <$> ask
        there <- act
        pure . safeInsert i here $ there

compTArgs :: CompT AbstractTy -> Int
compTArgs = \case
    CompN _ (ArgsAndResult args _) -> Vector.length args - 1

compTVars :: CompT AbstractTy -> [AbstractTy]
compTVars (CompN cnt _)
    | numVars == 0 = []
    | otherwise = map (BoundAt Z . unsafeIx) [0 .. (numVars - 1)]
  where
    numVars :: Int
    numVars = review intCount cnt

    unsafeIx :: Int -> Index "tyvar"
    unsafeIx i = fromJust $ preview intIndex i

-- We really should have a better way of doing this.
idToWord :: Id -> Word64
idToWord = toEnum . fromEnum

idToName :: Id -> Name
idToName i = Name ("x_" <> T.pack (show $ fromEnum i)) (Unique (fromEnum i))

{-

calculateLambdaTypes :: ASG -> Map LambdaId (Set AppId) -> Map LambdaId (Map AppId (Vector (ValT AbstractTy)))
calculateLambdaTypes asg = M.foldlWithKey' go M.empty
  where
    go :: Map LambdaId (Map AppId (Vector (ValT AbstractTy))) -> LambdaId -> Set AppId -> Map LambdaId (Map AppId (Vector (ValT AbstractTy)))
    go acc lid@(LambdaId lamId) appIds =
      let concreteVariants = M.fromSet mkConcrete appIds
      in M.insert lid concreteVariants acc
     where

       -- we're only ever using this on the arguments to an App, which have to be values. Right?
       resolveRefTy :: Ref -> ValT AbstractTy
       resolveRefTy = error "TODO: I assume I can write this?"

       {- We basically do this in `app` but then we throw the result away and we can't reuse the code here without exporting a TON of shit.

          (Though I think even if we could, it *might* not work for us, since iirc it tries to unify w/ the bb form, and here we don't want that)
       -}
       mkConcrete :: AppId -> Vector (ValT AbstractTy)
       mkConcrete (AppId appId) =
         let (appArgRefs,appInstTys) = case nodeAt appId asg of
                                 AValNode _ (App _ args instTs _) -> (args,instTs)
                                 anythingElse -> error $ "Fatal error: Expected app node, got " <> show anythingElse
             lamTy = case nodeAt lamId asg of
                       ACompNode lamT (Lam{}) -> lamT
                       anythingElse -> error $ "Fatal error: Expected a lambda node, got " <> show anythingElse

             appArgs :: Vector (ValT AbstractTy)
             appArgs = resolveRefTy <$> appArgRefs -- I assume I can write this?
         in case decideConcreteCompT lamTy of
           Just (compTBody -> ArgsAndResult args _)  -> vacuous <$> args
           Nothing ->
             let concretified  = concretifyLambdaTy lamTy appArgs
                 -- TODO/REVIEW/FIXME: We need to do *something* with the instantiations types.
                 --                    (We actually *have* to do something with them, we *can't* ignore them,
                 --                     it's impossible to reconstruct the correct function type w/o them in cases like the intro
                 --                     form for 'Left')
                 --                    It's easy enough to know what to do if the instantiation type is
                 --                    fully concrete (we don't even have to check it! it carries a proof),
                 --                    but it's not clear what to do if the instantiation type is a
                 --                    bound type variable (i.e. a rigid).
                 --
                 --                    This is the issue I'm trying to get at on slack. We can resolve the rigid to its *binding* context,
                 --                    i.e. the lambda node where it occurs, but to actually resolve it to something concrete, we have to look at
                 --                    potentially *every* call site for the binding context.
                 --
                 --                    We can do that if we need to... but it really complicates this. Instead of a
                 --                       Map LambdaId (Map AppId (Vector (ValT AbstractTy)))
                 --                    we have to return some
                 --                       Map LambdaId (Map ??? (Vector (ValT AbstractTy)))
                 --                    and that's what throws me: I don't know what we can use as an index
                 --                    that would actually allow us to refer to the right thing when we go to "insert all the
                 --                    lambda variants". I'm almost that *nothing* suffices to help us insert the right lambda
                 --                    in a bottom-up traversal for the  main codegen function, but (for other reasons) we
                 --                    really do want to do a bottom-up traversal there -_-
                 --
             in case traverse decideConcrete concretified  of
                  Just done -> vacuous <$> done
                  Nothing ->
                    error "WHAT DO WE DO HERE?"

{- Mostly adapted from Purus. This lets us avoid:
     1) Renaming here, which would be stupid.
     2) Exporting like all of the internal Unify module from Covenant
     3) Having to run all of this in an ASGBuilder-like monad
     4) Having to worry about weirdness that results from BB form unification that "disappears" in `checkApp` but which
        would almost certainly not disappear for us.

   We don't care about the return type so we ignore it.

-}
concretifyLambdaTy :: CompT AbstractTy -> Vector (ValT AbstractTy) -> Vector (ValT AbstractTy)
concretifyLambdaTy fn@(CompN _ (ArgsAndResult fnSig _)) args = runReader (traverse (substitute subs) args) 0
  where
    subs :: Map AbstractTy (ValT AbstractTy)
    subs =
      let fnTyVars = compTVars fn
          fnTys    = Vector.toList  fnSig
      in runReader (getInstantiations fnTyVars fnTys (Vector.toList args)) 0

resolveVar :: AbstractTy -> Reader Int AbstractTy
resolveVar (BoundAt db ix) = do
  offset <- ask
  let db' = fromJust . preview asInt $ review asInt db - offset
  pure $ BoundAt db' ix

instantiates :: AbstractTy
             -> ValT AbstractTy  -- the "more concrete type", usually the actual argument from 'app'
             -> ValT AbstractTy -- the "more polymorphic type', usually from the fn definition
             -> Reader Int (Maybe (ValT AbstractTy))
instantiates var concrete abstract = case (concrete,abstract) of
  (x,Abstraction a) -> sameVar var a >>= \case
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
  go (c:cs) (a:as) = (<|>) <$> instantiates var c a <*> go cs as

-- Given a list of variables, one list of types representing the function type (minus the result, we don't care about it i think),
-- and a second list of types representing the arguments to which it is applied, determine all the instantiations
-- I know we hate lists but it seems really silly to do this w/ vectors...
getInstantiations  :: [AbstractTy] -> [ValT AbstractTy] -> [ValT AbstractTy] -> Reader Int (Map AbstractTy (ValT AbstractTy))
getInstantiations [] _ _  = pure M.empty
getInstantiations _ [] _ = pure M.empty
getInstantiations _ _ [] = pure M.empty
getInstantiations (var:vars) fs@(fE:fEs) as@(aE:aEs) = instantiates var aE fE >>= \case
  Nothing -> (<>) <$> getInstantiations [var] fEs aEs <*> getInstantiations vars fs as
  Just t -> M.insert var t <$> getInstantiations vars fs as

substitute :: Map AbstractTy (ValT AbstractTy) -> ValT AbstractTy -> Reader Int (ValT AbstractTy)
substitute dict = \case
  Abstraction a -> resolveVar a >>= \a' -> case M.lookup a' dict of
    Nothing -> pure $ Abstraction a
    Just t -> pure t
  ThunkT (CompN cnt concreteFn) -> do
    let bodyAsVec = compTBodyToVec concreteFn
    subbedBody <- local (+ 1) $ traverse (substitute dict) bodyAsVec
    pure . ThunkT . CompN cnt $ vecToCompTBody subbedBody
  Datatype tn args -> Datatype tn <$> traverse (substitute dict) args
  other -> pure other

-}
