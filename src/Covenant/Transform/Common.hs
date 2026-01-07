{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Common (
    PolyRepHandler (..),
    lookupDatatypeInfo,
    lookupPolyRepHandler,
    resolvePolyRepHandler,
    AppTransformM (..),
    runAppTransformM,
    TyFixerFnData (..),
    TyFixerNodeKind (..),
    TyFixerDataBundle (..),
    nextId,
    freshName,
    freshNamePrefix,
    genLambdaArgNames,
    countToTyVars,
    pFreshLam,
    pFreshLam2,
    pLet,
    pFix,
    pCaseList,
    unsafeUnThunk,
    pCaseListWith,
    genFiniteListEliminator,
    pCaseConstrData,
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

import Covenant.ExtendedASG
import Covenant.MockPlutus (
    PlutusTerm,
    pApp,
    pCase,
    pFst,
    pLam,
    pSnd,
    pVar,
    unConstrData,
 )
import Covenant.Test (Id (UnsafeMkId))
import Covenant.Transform.Schema
import Covenant.Transform.TyUtils (idToName)
import Data.Foldable (
    foldl',
 )
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Text (Text)
import Data.Text qualified as T
import Optics.Core (preview, review)
import PlutusCore.Name.Unique (
    Name (Name),
    Unique (Unique),
 )

{- We need somewhere to stash these Ids (i.e. a reader context) since it's awkward to
   insert them into the ASG before we complete our analysis pass in the AppTranformM monad
-}
data PolyRepHandler = PolyRepHandler {project :: Id, embed :: Id} deriving stock (Show, Eq)

-- N.B. we need the `Map BuiltinFlatT Id` to record the projection/embedding function ids
-- TODO: Errors?
newtype AppTransformM a = AppTransformM (RWS (Map TyName (DatatypeInfo AbstractTy), Map BuiltinFlatT PolyRepHandler) () ExtendedASG a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadReader (Map TyName (DatatypeInfo AbstractTy), Map BuiltinFlatT PolyRepHandler)
        , MonadState ExtendedASG
        )
        via (RWS (Map TyName (DatatypeInfo AbstractTy), Map BuiltinFlatT PolyRepHandler) () ExtendedASG)

instance MonadASG AppTransformM where
    getASG = get
    putASG = put

runAppTransformM ::
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    ExtendedASG ->
    AppTransformM a ->
    (a, ExtendedASG)
runAppTransformM datatypes polyRepHandlers asg (AppTransformM act) = (x, i)
  where
    (x, i, _) = runRWS act (datatypes, polyRepHandlers) asg

-- stupid helpers

-- Something has gone really, horrifically wrong if something is annotated w/ a datatype type
-- and we don't know about the datatype at this point.
lookupDatatypeInfo :: TyName -> AppTransformM (DatatypeInfo AbstractTy)
lookupDatatypeInfo tn@(TyName tnInner) = do
    (dtDict, _) <- ask
    case M.lookup tn dtDict of
        Just res -> pure res
        Nothing -> error $ "No datatype info for " <> T.unpack tnInner

lookupPolyRepHandler :: ValT AbstractTy -> AppTransformM (Maybe PolyRepHandler)
lookupPolyRepHandler = \case
    BuiltinFlat biFlat -> do
        (_, repHandlerMap) <- ask
        pure $ M.lookup biFlat repHandlerMap
    _ -> pure Nothing

{- This is a helper for constructing a function which is used in all of the type fixer
   code generators to locate the correct plutus term corresponding to projection or embedding
   functions for a given type that potentially needs to be projected or embedded.

   In practice, locating this requires both:
     1. Information specific to the datatype. For type variables, we add the handlers as arguments to the
        type fixer "synthetic function".
     2. Generic information for statically known concrete builtin flat types, which we access from the AppTransformM
        monadic context.

   Largely a convenience b/c the implementation has to be somewhat ugly and is effectively duplicated several times.
-}
resolvePolyRepHandler :: -- Gets the projection or embedding we need (if it exists)
    TyFixerNodeKind ->
    -- Gives us the index into the list of terms representing
    -- function arguments which corresponds to the projection/embedding function
    Map (Index "tyvar") Int ->
    -- The thing we use the previous argument to index into; the arguments to the
    -- function-alized type fixer for the datatype.
    Vector PlutusTerm ->
    -- This is the index of the 'r' variable if we're in a catamorphism.
    -- This should ONLY be `Just` if we're working with a cata.
    -- We use this to determine whether to return 'self' (which
    -- is always the 0th element of the previous vector for a cata
    -- and which functions somewhat analogously to a projection/embedding function)
    Maybe (Index "tyvar") ->
    ValT AbstractTy ->
    AppTransformM (Maybe PlutusTerm)
resolvePolyRepHandler nodeKind handlerArgPosDict lamArgVars maybeR valT = case valT of
    Abstraction (BoundAt _ indx) -> case M.lookup indx handlerArgPosDict of
        Nothing -> case maybeR of
            Just rIndex | indx == rIndex -> pure . Just $ lamArgVars Vector.! 0
            _ -> pure Nothing
        Just hIx -> pure $ lamArgVars Vector.!? hIx
    bi@(BuiltinFlat _) -> do
        mRepHandler <- lookupPolyRepHandler bi
        case mRepHandler of
            Nothing -> pure Nothing
            Just polyRepHandler -> pure . Just . extractHandler $ polyRepHandler
    _anythingElse -> pure Nothing
  where
    extractHandler :: PolyRepHandler -> PlutusTerm
    extractHandler (PolyRepHandler projF embedF) = case nodeKind of
        MatchNode -> pVar . idToName $ projF
        CataNode -> pVar . idToName $ projF
        IntroNode -> pVar . idToName $ embedF

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

freshNamePrefix :: Text -> AppTransformM Name
freshNamePrefix nameBase = do
    UnsafeMkId w <- nextId
    let textPart = nameBase <> "_" <> T.pack (show w)
    pure $ Name textPart (Unique $ fromIntegral w)

genLambdaArgNames :: forall (a :: Type). Text -> Vector a -> AppTransformM (Vector Name)
genLambdaArgNames nameBase = Vector.imapM genTermVarName
  where
    genTermVarName :: Int -> a -> AppTransformM Name
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

pFreshLam2 :: (MonadASG m) => (PlutusTerm -> PlutusTerm -> m PlutusTerm) -> m PlutusTerm
pFreshLam2 f = do
    varName1 <- freshName
    varName2 <- freshName
    let argVar1 = pVar varName1
        argVar2 = pVar varName2
    body <- f argVar1 argVar2
    pure $ pLam varName1 (pLam varName2 body)

-- This will be useful eventually
pLet :: PlutusTerm -> (PlutusTerm -> AppTransformM PlutusTerm) -> AppTransformM PlutusTerm
pLet toBind withBind = do
    f <- pFreshLam withBind
    pure $ f `pApp` toBind

-- REVIEW: I can't remember whether Koz said to use a hoisted or non-hoisted fix -_-
pFix :: --
    PlutusTerm ->
    AppTransformM PlutusTerm
pFix f = do
    g <- pFreshLam (\r -> pure $ r `pApp` r)
    h <- pFreshLam (\r -> pure $ f `pApp` (r `pApp` r))
    pure $ g `pApp` h

-- This is for casing on a list that is known to NOT BE EMPTY
pCaseList ::
    PlutusTerm ->
    (PlutusTerm -> PlutusTerm -> AppTransformM PlutusTerm) ->
    AppTransformM PlutusTerm
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
    forall (a :: Type).
    [a] -> -- Usually a list of types representing the known structure of the list
    (a -> PlutusTerm -> AppTransformM PlutusTerm) -> -- what do we do with the head of the list?
    ([PlutusTerm] -> AppTransformM PlutusTerm) -> -- what do we do with all of the list elements at the end?
    PlutusTerm -> -- a list-typed plutus term
    AppTransformM PlutusTerm
pCaseListWith [] _ withElems _ = withElems [] -- only thing we can do
pCaseListWith (x : xs) withHead withElems aList = go [] aList x xs
  where
    go :: [PlutusTerm] -> PlutusTerm -> a -> [a] -> AppTransformM PlutusTerm
    go termAcc remList t [] = pCaseList remList $ \y _ys -> do
        yTerm <- withHead t y
        let args = termAcc <> [yTerm]
        withElems args
    go termAcc remList t (tx : ts) = pCaseList remList $ \y ys -> do
        yTerm <- withHead t y
        let termAcc' = termAcc <> [yTerm]
        go termAcc' ys tx ts

genFiniteListEliminator ::
    -- a Plutus term representing the branch/arm handler
    PlutusTerm ->
    -- The list (usually a scrutinee for Enums or the Plutus list of ctor args for a Constr encoded thing)
    PlutusTerm ->
    -- Looks up the projection/embedding/"self" function.
    (ValT AbstractTy -> AppTransformM (Maybe PlutusTerm)) ->
    -- The statically known types of all of the list elements
    [ValT AbstractTy] ->
    AppTransformM PlutusTerm
genFiniteListEliminator branchHandler aList resolveProjection elTys =
    pCaseListWith elTys withHead finalizer aList
  where
    withHead :: ValT AbstractTy -> PlutusTerm -> AppTransformM PlutusTerm
    withHead ty headEl =
        resolveProjection ty >>= \case
            Just projVar -> pure $ pApp projVar headEl
            Nothing -> pure headEl

    finalizer :: [PlutusTerm] -> AppTransformM PlutusTerm
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
    -- The scrutinee to case on. Needs to be ConstrData encoded PlutusData
    PlutusTerm ->
    -- A vector of types for each branch handler (in BB fn signature order)
    -- plus the corresponding handler (it will always be a variable)
    Vector (ValT AbstractTy, PlutusTerm) ->
    -- A function which selects unwrappers (or self recursive calls)
    -- for a given type variable.
    (ValT AbstractTy -> AppTransformM (Maybe PlutusTerm)) ->
    AppTransformM PlutusTerm
pCaseConstrData scrutinee typedHandlers lookupShim = do
    plcHandlers <- Vector.forM typedHandlers $ \(hTy, handler) -> do
        let hArgs = case hTy of
                ThunkT (CompN _ (ArgsAndResult args _)) -> Vector.toList args
                _ -> []
        genFiniteListEliminator handler ctorArgs lookupShim hArgs
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
