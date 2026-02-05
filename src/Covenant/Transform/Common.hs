{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Common (
    TyFixerFnData (..),
    TyFixerNodeKind (..),
    TyFixerDataBundle (..),
    tyFixerFnTy,
    nextId,
    freshName,
    freshNamePrefix,
    genLambdaArgNames,
    countToTyVars,
    pFreshLam,
    pFreshLam',
    pFreshLam2,
    pFreshLam2',
    pFreshLam3,
    pFreshLam3',
    pLetM,
    pLetM',
    pFix,
    pFix',
    pCaseList,
    unsafeUnThunk,
    pCaseListWith,
    genFiniteListEliminator,
    pCaseConstrData,
    BuiltinFnData (..),
    -- re-exports from Schema
    TypeSchema (..),
    schemaFnArgs,
    schemaFnType,
    mkTypeSchema,
) where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (MonadState (put), RWS, ask, runRWS)

import Covenant.ASG (
    Id,
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT,
    CompT (CompN),
    CompTBody (ArgsAndResult),
    DataEncoding,
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, ThunkT),
 )

import Control.Monad.Reader (MonadReader)
import Control.Monad.State.Strict (MonadState (get))
import Covenant.Data (DatatypeInfo)
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (Count, Index, intCount, intIndex)

import Covenant.ArgDict (pValT, pVec)
import Covenant.ExtendedASG
import Covenant.MockPlutus (
    PlutusTerm,
    pApp,
    pCase,
    pFst,
    pLam,
    pSnd,
    pVar,
    ppTerm,
    prettyPTerm,
    unConstrData,
    (#),
 )
import Covenant.Test (Id (UnsafeMkId))
import Covenant.Transform.Schema
import Covenant.Transform.TyUtils (idToName)
import Data.Bifunctor (Bifunctor (bimap, second))
import Data.Foldable (
    foldl',
 )
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Text (Text)
import Data.Text qualified as T

-- import Debug.Trace (traceM)
import Optics.Core (preview, review)
import PlutusCore.Name.Unique (
    Name (Name),
    Unique (Unique),
 )

traceM :: forall m. (Monad m) => String -> m ()
traceM _ = pure ()

prettyMap' :: (Show k, Show v) => Map k v -> String
prettyMap' = M.foldrWithKey (\k v acc -> show k <> " := " <> show v <> "\n" <> acc) "\n"

{- This records the information we need for our "mock" functions for catamorphisms/datatype intro/datatype elimination

   Specifically, it contains:
     1. The type name. For catas and matches, this is the type of the "scrutinee" being matched on, for intros it is the result
     2. The encoding. This will be useful later on.
     3. The FULLY POLYMORPHIC type of the function
     4. A PLC term corresponding to the function
     5. A token indicating which "sort" of function it is (cata/match/intro). This will also contain the "true"
        function type, which takes additional wrapper/unwrapper arguments IF THE TYPE IS DATA ENCODED.
        This is the type of the PLC term, but we "lie" about it when we replace the match/cata/intro with an app so as to use the existing machinery.
     6. The name of the function.

     Some explanation for 4: For example, if we have a data encoded Maybe type, the "false" types would be:
       match_Maybe :: forall a r. Maybe a -> r -> (a -> r) -> r
       Just :: forall a. a -> Maybe a
       Nothing :: forall a. Maybe a
       (.. maybe doesn't have a catamorphism form ...)

     But the "true" types w/ the handler arguments are:
       match_Maybe :: forall a r. Maybe a -> r -> (a -> r) -> (a -> a) -> r
       Just :: forall a. Maybe a -> (a -> a) -> a
       Nothing :: forall a. Maybe a

     In `match_Maybe` the extra argument will be either an identity function if the type is not a representationally amorphous
     primitive, or an unwrapper like `unI` or `unB` if the parameter is a representationally amorphous primitive.

     In the constructor forms (or at least the ones for non-nullary constructors), the extra arg will be an `I` or `B` wrapper.
-}
data TyFixerFnData
    = TyFixerFnData
        { mfTyName :: TyName
        , mfEncoding :: DataEncoding
        , mfPolyType :: CompT AbstractTy
        , mfCompiled :: PlutusTerm
        , mfTypeSchema :: TypeSchema
        , mfFunName :: Text
        , mfNodeKind :: TyFixerNodeKind
        }
    | BuiltinTyFixer (CompT AbstractTy) BuiltinFnData

tyFixerFnTy :: TyFixerFnData -> CompT AbstractTy
tyFixerFnTy = \case
    TyFixerFnData _ _ ty _ _ _ _ -> ty
    BuiltinTyFixer ty _ -> ty

-- BuiltinFnData holds the information we need to compile every "compiler primitive" non-atomic datatype.
-- This is needed in large part because we cannot generate a corresponding Plutus Term for parametric
-- builtins (mainly List) until we've already completed an analysis that comes after the type fixer transform
-- (this could be avoided, probably, but I don't have time)
-- We don't need to stash any information inside of these. We just need to know which Ids point at which of them,
-- and have a computation type we can use for analysis.
data BuiltinFnData
    = -- Constructors
      List_Cons
    | List_Nil
    | Data_I
    | Data_B
    | Data_List
    | Data_Map
    | Data_Constr
    | Pair_Pair
    | Map_Map
    | -- Catamorphisms
      Integer_Nat_Cata
    | Integer_Neg_Cata
    | List_Cata
    | ByteString_Cata
    | -- Eliminators
      List_Match
    | Pair_Match
    | Map_Match
    | Data_Match
    deriving stock (Show, Eq)

data TyFixerNodeKind = MatchNode | IntroNode | CataNode
    deriving stock (Show, Eq, Ord)

{- Need some kind of structured container for holding the results of our
   generated data for functionalized type fixers.

   I *think* that every datatype (other than Void, which doesn't matter, because it can't exist
   as a term to match on or introduce) should end up having IntroData and MatchData, but only recursive types get a
   CataData.

-}
data TyFixerDataBundle
    = TyFixerDataBundle
    { introData :: Vector TyFixerFnData
    , matchData :: Maybe TyFixerFnData
    , cataData :: Maybe TyFixerFnData
    }

freshName :: (MonadASG m) => m Name
freshName = do
    UnsafeMkId w <- nextId
    let textPart = "var_" <> T.pack (show w)
        asName = Name textPart (Unique $ fromIntegral w)
    pure asName

freshNamePrefix :: (MonadASG m) => Text -> m Name
freshNamePrefix nameBase = do
    UnsafeMkId w <- nextId
    let textPart = nameBase <> "_" <> T.pack (show w)
    pure $ Name textPart (Unique $ fromIntegral w)

genLambdaArgNames ::
    forall (m :: Type -> Type) (a :: Type).
    (MonadASG m) =>
    Text ->
    Vector a ->
    m (Vector Name)
genLambdaArgNames nameBase = Vector.imapM genTermVarName
  where
    genTermVarName :: Int -> a -> m Name
    genTermVarName pos _ = do
        UnsafeMkId i <- nextId
        let textPart = nameBase <> "_arg" <> T.pack (show pos)
            uniquePart = Unique (fromIntegral i)
        pure $ Name textPart uniquePart

countToTyVars :: Count "tyvar" -> Vector (ValT AbstractTy)
countToTyVars cnt
    | cntI == 0 = mempty
    | otherwise = mkTV <$> Vector.fromList [0 .. (cntI - 1)]
  where
    cntI :: Int
    cntI = review intCount cnt

    mkTV :: Int -> ValT AbstractTy
    mkTV = Abstraction . BoundAt Z . fromJust . preview intIndex

-- We could probably steal the plutarch typeclass trick to get arbitrary embedded lambdas... but
-- that's overkill here
pFreshLam :: (MonadASG m) => (PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pFreshLam f = do
    varName <- freshName
    let argVar = pVar varName
    pLam varName <$> f argVar

pFreshLam' :: (MonadASG m) => Text -> (PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pFreshLam' nm f = do
    varName <- freshNamePrefix nm
    let argVar = pVar varName
    pLam varName <$> f argVar

pFreshLam2 :: (MonadASG m) => (PlutusTerm -> PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pFreshLam2 f = do
    varName1 <- freshName
    varName2 <- freshName
    let argVar1 = pVar varName1
        argVar2 = pVar varName2
    body <- f argVar1 argVar2
    pure $ pLam varName1 (pLam varName2 body)

pFreshLam2' ::
    (MonadASG m) =>
    Text ->
    Text ->
    (PlutusTerm -> PlutusTerm -> m PlutusTerm) ->
    m PlutusTerm
pFreshLam2' vn1 vn2 f = do
    varName1 <- freshNamePrefix vn1
    varName2 <- freshNamePrefix vn2
    let argVar1 = pVar varName1
        argVar2 = pVar varName2
    body <- f argVar1 argVar2
    pure $ pLam varName1 (pLam varName2 body)

pFreshLam3 :: (MonadASG m) => (PlutusTerm -> PlutusTerm -> PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pFreshLam3 f = do
    v1 <- freshName
    v2 <- freshName
    v3 <- freshName
    let arg1 = pVar v1
        arg2 = pVar v2
        arg3 = pVar v3
    body <- f arg1 arg2 arg3
    pure $ pLam v1 (pLam v2 (pLam v3 body))

pFreshLam3' ::
    (MonadASG m) =>
    Text ->
    Text ->
    Text ->
    (PlutusTerm -> PlutusTerm -> PlutusTerm -> m PlutusTerm) ->
    m PlutusTerm
pFreshLam3' vn1 vn2 vn3 f = do
    v1 <- freshNamePrefix vn1
    v2 <- freshNamePrefix vn2
    v3 <- freshNamePrefix vn3
    let arg1 = pVar v1
        arg2 = pVar v2
        arg3 = pVar v3
    body <- f arg1 arg2 arg3
    pure $ pLam v1 (pLam v2 (pLam v3 body))

-- This will be useful eventually
pLetM :: (MonadASG m) => PlutusTerm -> (PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pLetM toBind withBind = do
    f <- pFreshLam withBind
    pure $ f `pApp` toBind

pLetM' :: (MonadASG m) => Text -> PlutusTerm -> (PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pLetM' nm toBind withBind = do
    f <- pFreshLam' nm withBind
    pure $ f `pApp` toBind

-- REVIEW: I can't remember whether Koz said to use a hoisted or non-hoisted fix -_-
pFix ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    PlutusTerm ->
    m PlutusTerm
pFix f = do
    g <- pFreshLam' "fix_x" $ \r -> pure (r # r)
    h <- pFreshLam' "fix_y" (\r -> pure $ f # (r # r))
    pure $ g # h

pFix' ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    m PlutusTerm
pFix' = pFreshLam' "fix_f" $ \f -> do
    g <- pFreshLam' "fix_x" $ \r -> pure (r # r)
    h <- pFreshLam' "fix_y" (\r -> pure $ f # (r # r))
    pure $ g # h

-- This is for casing on a list that is known to NOT BE EMPTY
pCaseList ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    PlutusTerm ->
    (PlutusTerm -> PlutusTerm -> m PlutusTerm) ->
    m PlutusTerm
pCaseList xs f = pCase xs . Vector.singleton <$> pFreshLam2 f

-- Used to resolve some annoying inconsistencies we don't have time to fix now
unsafeUnThunk :: ValT AbstractTy -> CompT AbstractTy
unsafeUnThunk = \case
    ThunkT compTy -> compTy
    other -> error $ "Tried to un-thunk a non-thunk value: " <> show other

{- Does this, basically:

   list = [Int,String,Bool]

   case list [\x xs -> case xs [\y ys -> case ys -> [\z _zs -> f x y z]]]

-}
pCaseListWith ::
    forall (a :: Type) (m :: Type -> Type).
    (MonadASG m) =>
    [a] -> -- Usually a list of types representing the known structure of the list
    (a -> PlutusTerm -> m PlutusTerm) -> -- what do we do with the head of the list?
    ([PlutusTerm] -> m PlutusTerm) -> -- what do we do with all of the list elements at the end?
    PlutusTerm -> -- a list-typed plutus term
    m PlutusTerm
pCaseListWith [] _ withElems _ = withElems [] -- only thing we can do
pCaseListWith (x : xs) withHead withElems aList = go [] aList x xs
  where
    go :: [PlutusTerm] -> PlutusTerm -> a -> [a] -> m PlutusTerm
    go termAcc remList t [] = pCaseList remList $ \y _ys -> do
        yTerm <- withHead t y
        let args = termAcc <> [yTerm]
        withElems args
    go termAcc remList t (tx : ts) = pCaseList remList $ \y ys -> do
        yTerm <- withHead t y
        let termAcc' = termAcc <> [yTerm]
        go termAcc' ys tx ts

genFiniteListEliminator ::
    forall m.
    (MonadASG m) =>
    -- a Plutus term representing the branch/arm handler
    PlutusTerm ->
    -- The list (usually a scrutinee for Enums or the Plutus list of ctor args for a Constr encoded thing)
    PlutusTerm ->
    -- Looks up the projection/embedding/"self" function.
    (ValT AbstractTy -> m (Maybe PlutusTerm)) ->
    -- The statically known types of all of the list elements
    [ValT AbstractTy] ->
    m PlutusTerm
genFiniteListEliminator branchHandler aList resolveProjection elTys =
    pCaseListWith elTys withHead finalizer aList
  where
    withHead :: ValT AbstractTy -> PlutusTerm -> m PlutusTerm
    withHead ty headEl =
        resolveProjection ty >>= \case
            Just projVar -> do
                let result = pApp projVar headEl
                let msg =
                        "\nresolveProjection SUCCESS\n  ty: "
                            <> pValT ty
                            <> "\n  term: "
                            <> ppTerm headEl
                            <> "\n  result: "
                            <> ppTerm result
                traceM msg
                pure $ pApp projVar headEl
            Nothing -> do
                let msg =
                        "\nresolveProjection FAIL\n  ty: "
                            <> pValT ty
                            <> "\n  term: "
                            <> ppTerm headEl
                            <> "\n  result: "
                            <> ppTerm headEl
                traceM msg
                pure headEl

    finalizer :: [PlutusTerm] -> m PlutusTerm
    finalizer = pure . foldl' pApp branchHandler

{- This is a convenience helper for generating case expressions over constructor encoded datatypes which
   are (hopefully) fairly performant.

   The idea is that if you have a data encoded type such as

   `data List a = Nil | Cons a (List a)`

   with a BBF such as

   `forall a r. r -> (a -> r -> r) -> r`

   We need to codegen functions for catamorphisms and pattern matches which look, broadly, like

   \scrutinee doNil doCons projectA -> case (fstPair (unConstrData scrutinee)) of
     0 -> doNil
     1 -> case (sndPair (unConstrData scrutinee)) of
       aList -> case aList [\x xs -> doCons (project x) xs]

   (I'm mashing together notation there, apologies, but I hope the idea is clear.)

   This only generates the *body* of the function we need, and to get the above output here, we want to call it like

   `pCaseConstrData scrutinee [(r,doNil),(a -> r -> r, doCons)] project`

-}
pCaseConstrData ::
    forall m.
    (MonadASG m) =>
    -- The scrutinee to case on. Needs to be ConstrData encoded PlutusData
    PlutusTerm ->
    -- A vector of types for each branch handler (in BB fn signature order)
    -- plus the corresponding handler (it will always be a variable)
    Vector (ValT AbstractTy, PlutusTerm) ->
    -- A function which selects unwrappers (or self recursive calls)
    -- for a given type variable.
    (ValT AbstractTy -> m (Maybe PlutusTerm)) ->
    m PlutusTerm
pCaseConstrData scrutinee typedHandlers lookupShim = do
    plcHandlers <- Vector.forM typedHandlers $ \(hTy, handler) -> do
        let hArgs = case hTy of
                ThunkT (CompN _ (ArgsAndResult args _)) -> Vector.toList args
                _ -> []
        genFiniteListEliminator handler ctorArgs lookupShim hArgs
    traceM $
        "\npCaseConstrData: \n  scrut: "
            <> ppTerm scrutinee
            <> "\n  typedHandlers: "
            <> show (bimap pValT ppTerm <$> typedHandlers)
            <> "\n  resolvedHandlers: "
            <> pVec ppTerm plcHandlers
    pure $ pCase ctorIx plcHandlers
  where
    constrDataPair = unConstrData scrutinee
    ctorIx = pFst constrDataPair
    ctorArgs = pSnd constrDataPair

{- Given a branch handler, a scrutinee, a way to lookup the projection function, and a list of types representing the
   Covenant types of elements, construct an expression that extracts the arguments from the handler and applies the handler
   to them.

   NOTE: This is kind of crude. It'll end up as a smorgasbord of nested calls to `head` and `tail`. We could
         probably do a lot better than this somehow? But this is the *easiest* way I can think of.

genFiniteListEliminator :: -- The branch handler function as a plutus term
    PlutusTerm ->
    -- The scrutinee (or the argument list for a Constr-encoded data thing)
    PlutusTerm ->
    -- Looks up the right projection function
    (ValT AbstractTy -> Maybe PlutusTerm) ->
    -- The types of the list elements
    [ValT AbstractTy] ->
    PlutusTerm
genFiniteListEliminator branchHandler scrutinee resolveProjection elTys =
    foldl' pApp branchHandler $ genFiniteListElimArgs scrutinee elTys
  where
    genFiniteListElimArgs :: -- The "remainder" of the list (usually an application of tail to the original scrutinee)
        PlutusTerm ->
        -- the types of the remainder of the list
        [ValT AbstractTy] ->
        [PlutusTerm]
    genFiniteListElimArgs remList [] = [] -- nothing left to do
    -- \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/
    -- FIXME/TODO/REVIEW/BUG: THIS WONT WORK!!! Inside the handlers the DeBruijn index will always
    --                        Be 1 higher. We need to adjust DB indices here before we try to look up
    --                        the projection for a given ValT.
    genFiniteListElimArgs remList (t : ts) = case resolveProjection t of
        Nothing -> pHead remList : genFiniteListElimArgs (pTail remList) ts
        Just unwrapper -> pApp unwrapper (pHead remList) : genFiniteListElimArgs (pTail remList) ts
        -- [head xs, head (tail xs), head (tail (tail xs))]
-- /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\
-}
