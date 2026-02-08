{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Transform.TyUtils
  ( AppId (..),
    LambdaId (..),
    countToTyVars,
    countToAbstractions,
    idToName,
    applyArgs,
    substCompT,
    runSubst,
    isConcrete,
    getInstantiations,
    collectRigids,
    cleanup,
    assertConcrete,
  )
where

import Control.Applicative (Alternative ((<|>)))
import Control.Monad.RWS.Strict (ask, local)
import Control.Monad.Reader (Reader, runReader)
import Covenant.ASG (Id)
import Covenant.DeBruijn (DeBruijn (Z), asInt)
import Covenant.Index (Count, intCount, intIndex)
import Covenant.Test (Id (UnsafeMkId))
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (CompN),
    CompTBody (ArgsAndResult, ReturnT),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
  )
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust, isJust)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Void (Void)
import Optics.Core (preview, review)
import UntypedPlutusCore (Name (Name), Unique (Unique))

newtype LambdaId = LambdaId {_getLamId :: Id}
  deriving newtype (Show, Eq, Ord)

newtype AppId = AppId {_getAppId :: Id}
  deriving newtype (Show, Eq, Ord)

-- Just saves us the hassle of having to runReader and local a bunch
runSubst :: forall (a :: Type). Int -> (ValT a -> ValT AbstractTy) -> Map AbstractTy (ValT a) -> ValT AbstractTy -> ValT AbstractTy
runSubst dbStart f subDict val = flip runReader dbStart $ substitute f subDict val

idToName :: Id -> Name
idToName i = Name ("x_" <> T.pack (show $ fromEnum i)) (Unique (fromEnum i))

compTBodyToVec :: forall a. CompTBody a -> Vector (ValT a)
compTBodyToVec (ArgsAndResult args res) = Vector.snoc args res

compTBody :: CompT a -> CompTBody a
compTBody (CompN _ body) = body

compTArgSchema :: CompT a -> Vector (ValT a)
compTArgSchema t = case compTBody t of
  ArgsAndResult args _ -> args

vecToCompTBody :: forall a. Vector (ValT a) -> CompTBody a
vecToCompTBody vec = case Vector.unsnoc vec of
  Just (args, res)
    | Vector.null args -> ReturnT res -- might not need this?
    | otherwise -> ArgsAndResult args res
  Nothing -> error "empty CompT"

decideConcrete :: ValT AbstractTy -> Maybe (ValT Void)
decideConcrete = \case
  Abstraction _ -> Nothing
  ThunkT (CompN cnt body) -> do
    body' <- traverse decideConcrete $ compTBodyToVec body
    pure . ThunkT . CompN cnt $ vecToCompTBody body'
  BuiltinFlat biTy -> Just (BuiltinFlat biTy)
  Datatype tn args -> Datatype tn <$> traverse decideConcrete args

isConcrete :: ValT AbstractTy -> Bool
isConcrete = isJust . decideConcrete

-- unsafe, but we should only ever end up using this on things we've had to "downcast" from ValT Void to ValT AbstractTy
assertConcrete :: ValT AbstractTy -> ValT Void
assertConcrete = fromJust . decideConcrete

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
      BuiltinFlat {} -> pure S.empty
      Datatype _ args -> mconcat <$> traverse go (Vector.toList args)

{- This is a kind of improvised unification where we know that one side is necessarily more polymorphic than the other
   (and that the other can only contain rigid type variables or concrete types).
-}
applyArgs :: CompT AbstractTy -> [ValT AbstractTy] -> CompT AbstractTy
applyArgs compT [] = compT
-- I *think* we ignore the result when determining the substitutions and then substitute into it to reconstruct
-- the type.
applyArgs polyFun@(CompN cnt (ArgsAndResult fnSigArgs _)) args = cleanup concreteFn
  where
    vars :: [AbstractTy]
    vars = Vector.toList $ countToAbstractions cnt

    instantiations :: Map AbstractTy (ValT AbstractTy)
    instantiations =
      flip runReader 0 $
        getInstantiations vars (Vector.toList fnSigArgs) args

    concreteFn :: CompT AbstractTy
    concreteFn = substCompT id instantiations polyFun

{- Our analogue of 'fixUp' from the unification module, but done without renaming (b/c we can't rename here, really) -}
cleanup :: CompT AbstractTy -> CompT AbstractTy
cleanup origFn@(CompN cnt (ArgsAndResult args result)) = case substCompT id substitutions origFn of
  CompN _ body -> CompN newCount body
  where
    newCount :: Count "tyvar"
    newCount = fromJust . preview intCount $ Vector.length remainingLocalVars

    fnSig :: Vector (ValT AbstractTy)
    fnSig = Vector.snoc args result

    allOriginalVars :: Set AbstractTy
    allOriginalVars = Set.fromList . Vector.toList $ countToAbstractions cnt

    substitutions :: Map AbstractTy (ValT AbstractTy)
    substitutions =
      Vector.ifoldl'
        ( \acc newIx oldTV ->
            let tvIx = fromJust $ preview intIndex newIx
                newTv = Abstraction (BoundAt Z tvIx)
             in M.insert oldTV newTv acc
        )
        M.empty
        remainingLocalVars

    remainingLocalVars :: Vector AbstractTy
    remainingLocalVars =
      Vector.fromList
        . Set.toList
        . Set.unions
        . flip runReader 0
        . traverse collectLocalVars
        . Vector.toList
        $ fnSig

    collectLocalVars :: ValT AbstractTy -> Reader Int (Set AbstractTy)
    collectLocalVars = \case
      Abstraction a -> do
        resolved <- resolveVar a
        if resolved `Set.member` allOriginalVars
          then pure $ Set.singleton a
          else pure Set.empty
      BuiltinFlat {} -> pure Set.empty
      ThunkT (CompN _ (ArgsAndResult thunkArgs thunkRes)) -> local (+ 1) $ do
        let toTraverse = Vector.toList $ Vector.snoc thunkArgs thunkRes
        Set.unions <$> traverse collectLocalVars toTraverse
      Datatype _ dtArgs -> Set.unions <$> traverse collectLocalVars (Vector.toList dtArgs)

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

countToTyVars :: Count "tyvar" -> Vector (ValT AbstractTy)
countToTyVars cnt
  | cntI == 0 = mempty
  | otherwise = mkTV <$> Vector.fromList [0 .. (cntI - 1)]
  where
    cntI :: Int
    cntI = review intCount cnt

    mkTV :: Int -> ValT AbstractTy
    mkTV = Abstraction . BoundAt Z . fromJust . preview intIndex

countToAbstractions :: Count "tyvar" -> Vector AbstractTy
countToAbstractions cnt
  | cntI == 0 = mempty
  | otherwise = mkTV <$> Vector.fromList [0 .. (cntI - 1)]
  where
    cntI :: Int
    cntI = review intCount cnt

    mkTV :: Int -> AbstractTy
    mkTV = BoundAt Z . fromJust . preview intIndex

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
