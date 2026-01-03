{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, asks, execRWS, local, modify)

import Covenant.ASG (
    ASG (ASG),
    ASGNode (ACompNode, AValNode, AnError),
    ASGNodeType (ValNodeType),
    BoundTyVar,
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId,
    typeASGNode,
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp1, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataConstructor (..),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar,
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (MonadReader, Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), State, StateT, evalState, execState, gets, modify', runState)
import Covenant.ArgDict (idToName)
import Covenant.Data (DatatypeInfo, mkCataFunTy, mkMatchFunTy)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count2, intCount, intIndex, ix0, ix1, wordCount)
import Covenant.MockPlutus (
    PlutusTerm,
    constrData,
    listData,
    pApp,
    pCase,
    pConstr,
    pFst,
    pHead,
    pLam,
    pSnd,
    pTail,
    pVar,
    plutus_I,
    unConstrData,
    unIData,
    unListData,
 )
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (ForceInternal, LamInternal), Id (UnsafeMkId), ValNodeInfo (AppInternal), unsafeMkDatatypeInfos)
import Data.Foldable (
    find,
    foldl',
    traverse_,
 )
import Data.Kind (Type)
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, over, preview, review, set, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

import Covenant.JSON

import Control.Monad (foldM)
import Control.Monad.Writer.Strict (MonadWriter)
import Covenant.Concretify (countToAbstractions, getInstantiations, resolveVar, substCompT)
import Covenant.ExtendedASG
import Covenant.JSON (CompilationUnit (..))
import Covenant.Transform.Cata
import Covenant.Transform.Common
import Covenant.Transform.Elim
import Covenant.Transform.Intro
import Data.Bifunctor (Bifunctor (first, second))
import Data.Row.Dictionaries qualified as R
import Data.Row.Records (HasType, Rec, Row, (.+), (.==), type (.+), type (.-), type (.==))
import Data.Row.Records qualified as R
import Data.Set qualified as Set

transformASG :: CompilationUnit -> (Rec ASGMetaData, ExtendedASG)
transformASG (CompilationUnit datatypes asg _) = flip runState extended $ do
    let dtDict = unsafeMkDatatypeInfos (Vector.toList datatypes)
    firstPassMeta <- mkProjectionsAndEmbeddings
    let builtinHandlers = firstPassMeta R..! #builtinHandlers
    tyFixerData <- mkTypeFixerFnData dtDict builtinHandlers
    toTransform <- getASG
    let transformState :: Rec TransformState
        transformState =
            firstPassMeta
                .+ #asg .== toTransform
                .+ #dtDict .== dtDict
                .+ #visited .== S.empty
                .+ #tyFixerData .== tyFixerData

    finalMeta <- snd <$> unliftMetaM transformState transformTypeFixerNodes
    pure finalMeta
  where
    extended :: ExtendedASG
    extended = wrapASG asg

-- I didn't bill for the row stuff, I just got frustrated having to rewrite optics over and over again
-- as I iterated heavily on this module and used this out for convenience while experimenting. I can remove it all later.
unliftMetaM ::
    forall
        (m :: Type -> Type)
        (r :: Row Type)
        (a :: Type).
    (HasType "asg" ExtendedASG r, R.AllUniqueLabels r, MonadASG m, Monad m) =>
    Rec r -> MetaM r a -> m (a, Rec r)
unliftMetaM r act = do
    asg <- getASG
    let rIn = R.update #asg asg r
        (a, rOut) = runMetaM rIn act
    putASG (rOut R..! #asg)
    pure (a, rOut)

type ASGMetaData =
    "builtinHandlers" .== Map BuiltinFlatT PolyRepHandler
        .+ "identityFn" .== ExtendedId
        .+ "uniqueError" .== ExtendedId
        .+ "asg" .== ExtendedASG
        .+ "dtDict" .== Map TyName (DatatypeInfo AbstractTy)
        .+ "visited" .== Set ExtendedId
        .+ "tyFixerData" .== Map TyName TyFixerDataBundle

newtype MetaM r a = MetaM (State (Rec r) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadState (Rec r)
        )
        via (State (Rec r))

instance (HasType "asg" ExtendedASG r) => MonadASG (MetaM r) where
    getASG = gets (R..! #asg)
    putASG asg = modify' $ R.update #asg asg

runMetaM :: forall (r :: Row Type) (a :: Type). Rec r -> MetaM r a -> (a, Rec r)
runMetaM aRec (MetaM act) = runState act aRec

-- From here on out the top level node CANNOT BE ASSUMED TO BE THE HIGHEST NODE NUMERICALLY.
-- This is annoying but there really isn't a sensible way around it.
--
-- We also have to remember to "catch" the IDs for these functions during codegen
-- since they won't have a body, so we're going to have to keep the map around for a while too.
--
-- sorry koz
type FirstPassMeta =
    "builtinHandlers" .== Map BuiltinFlatT PolyRepHandler
        .+ "identityFn" .== ExtendedId
        .+ "uniqueError" .== ExtendedId
mkProjectionsAndEmbeddings :: forall (m :: Type -> Type). (MonadASG m) => m (Rec FirstPassMeta)
mkProjectionsAndEmbeddings = do
    uniqueErrorId <- ephemeralErrorId
    identityId <- mkIdentityFn
    eInsert uniqueErrorId AnError
    polyRepHandlers <- M.unions <$> traverse (mkRepHandler uniqueErrorId) [IntegerT, ByteStringT]
    pure $
        #builtinHandlers .== polyRepHandlers
            .+ #identityFn .== identityId
            .+ #uniqueError .== uniqueErrorId
  where
    mkRepHandler :: ExtendedId -> BuiltinFlatT -> m (Map BuiltinFlatT PolyRepHandler)
    mkRepHandler errId t = do
        projT <- projectionId
        embedT <- embeddingId
        let synthFnTy = Comp0 $ BuiltinFlat t :--:> ReturnT (BuiltinFlat t)
            synthFnNode = syntheticLamNode (UniqueError . forgetExtendedId $ errId) synthFnTy
        eInsert projT synthFnNode
        eInsert embedT synthFnNode
        pure $ M.singleton t (PolyRepHandler (forgetExtendedId projT) (forgetExtendedId embedT))

    mkIdentityFn :: m ExtendedId
    mkIdentityFn = do
        idFnId <- identityFnId
        let compNode = ACompNode (Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) (LamInternal (AnArg (UnsafeMkArg Z ix0 (tyvar Z ix0))))
        eInsert idFnId compNode
        pure idFnId
unsafeNextId :: Id -> Id
unsafeNextId (UnsafeMkId i) = UnsafeMkId (i + 1)

mkTypeFixerFnData ::
    forall m.
    (MonadASG m) =>
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    m (Map TyName TyFixerDataBundle)
mkTypeFixerFnData datatypes biRepHandlers =
    liftAppTransformM $ do
        let allTyNames = M.keys datatypes
        foldM go M.empty allTyNames
  where
    liftAppTransformM :: AppTransformM a -> m a
    liftAppTransformM act = do
        asg <- getASG
        let (res, newASG) = runAppTransformM datatypes biRepHandlers asg act
        putASG newASG
        pure res

    go :: Map TyName TyFixerDataBundle -> TyName -> AppTransformM (Map TyName TyFixerDataBundle)
    go acc tn = do
        destructorData <- mkDestructorFunction tn
        constructorData <- mkConstructorFunctions tn
        -- If we have no constructor functions nor match functions, our datatype is 'void' and we can ignore it
        if null destructorData && null constructorData
            then pure acc
            else do
                cataData <- mkCatamorphism tn
                let thisBundle = TyFixerDataBundle constructorData destructorData cataData
                pure $ M.insert tn thisBundle acc

    mkTypeFixerLookupTable :: Map Id TyFixerFnData -> Map TyName Id
    mkTypeFixerLookupTable = M.foldlWithKey' (\acc i tffData -> M.insert (mfTyName tffData) i acc) M.empty

-- Just to help me keep straight all of the various IDs we need to keep track of
newtype UniqueError = UniqueError Id

{- Rewrites type fixer nodes into applications.

   This also constructs and inserts dummy functions into the ASG
-}
type TransformState =
    FirstPassMeta
        .+ "asg" .== ExtendedASG
        .+ "visited" .== Set ExtendedId
        .+ "dtDict" .== Map TyName (DatatypeInfo AbstractTy)
        .+ "tyFixerData" .== Map TyName TyFixerDataBundle
transformTypeFixerNodes ::
    forall (m :: Type -> Type).
    MetaM TransformState ()
transformTypeFixerNodes = do
    topSrcNode <- fst <$> (eTopLevelSrcNode :: MetaM TransformState (ExtendedId, ASGNode))
    go topSrcNode --  dtDict magicErr tyFixers
  where
    conjureFunction :: CompT AbstractTy -> MetaM TransformState ASGNode
    conjureFunction compT = do
        errId <- forgetExtendedId <$> gets (R..! #uniqueError)
        pure $ syntheticLamNode (UniqueError errId) compT

    resolveCtorIx :: TyName -> ConstructorName -> MetaM TransformState (Maybe Int)
    resolveCtorIx tn cn = do
        dtInfo <- (M.! tn) <$> gets (R..! #dtDict)
        case view #originalDecl dtInfo of
            OpaqueData _ ctors -> do
                -- TODO/REVIEW: NEED TO CHECK THAT THIS NAMING IS CONSISTENT WITH ANYWHERE ELSE WE HANDLE THIS
                let (ConstructorName inner) = cn
                    mplutusDataCtor = case inner of
                        "I" -> Just PlutusI
                        "B" -> Just PlutusB
                        "Constr" -> Just PlutusConstr
                        "List" -> Just PlutusList
                        "Map" -> Just PlutusMap
                        _ -> Nothing
                case mplutusDataCtor of
                    Nothing -> pure Nothing
                    Just plutusDataCtor ->
                        pure $ Vector.findIndex (== plutusDataCtor) (Vector.fromList . Set.toList $ ctors)
            DataDeclaration _ _ ctors _ -> pure $ Vector.findIndex (\(Constructor cNm' _) -> cNm' == cn) ctors

    -- this should only be used in contexts where we must have a datatype (e.g. scrutinees in matches and catas, parts of generated functions)
    unsafeDatatypeName :: ValT AbstractTy -> TyName
    unsafeDatatypeName = \case
        Datatype tn _ -> tn
        other -> error $ "unsafeDatatypeName called on non-datatype ValT: " <> show other

    -- only use this on things that have to be a value type (i.e. scrutinees)
    unsafeRefType :: Ref -> MetaM TransformState (ValT AbstractTy)
    unsafeRefType = \case
        AnArg (UnsafeMkArg _ _ ty) -> pure ty
        AnId i ->
            eNodeAt i >>= \node -> case typeASGNode node of
                ValNodeType ty -> pure ty
                other -> error $ "UnsafeRefType called on an Id with a non-ValT type: " <> show other

    alreadyVisited :: ExtendedId -> MetaM TransformState Bool
    alreadyVisited i = S.member i <$> gets (R..! #visited)

    insertAndMarkVisited :: ExtendedId -> ASGNode -> MetaM TransformState ()
    insertAndMarkVisited eid node = do
        eInsert eid node
        oldVisited <- gets (R..! #visited)
        modify' $ R.update #visited (S.insert eid oldVisited)

    go :: ExtendedId -> MetaM TransformState ()
    go i =
        alreadyVisited i >>= \case
            True -> pure ()
            False ->
                eNodeAt i >>= \case
                    AnError -> pure ()
                    ACompNode compT compNode -> case compNode of
                        Lam ref -> goRef ref
                        Force ref -> goRef ref
                        _ -> pure ()
                    AValNode valT valNode -> case valNode of
                        Thunk child -> resolveExtended child >>= go
                        App fn args _ _ -> do
                            resolveExtended fn >>= go
                            traverse_ goRef args
                        Cata cataT handlers arg -> do
                            traverse_ goRef handlers
                            goRef arg
                            -- TODO: Maybe we should check visited again here? Really we should recurse at the end, probably, but
                            --       it makes this code really annoying to read -_-
                            tyFixers <- gets (R..! #tyFixerData)
                            tn <- unsafeDatatypeName <$> unsafeRefType arg
                            case cataData =<< M.lookup tn tyFixers of
                                Nothing ->
                                    error $
                                        "Fatal Error: No type fixer function data for catamorphisms on " <> show tn
                                Just (TyFixerFnData _nm _enc cataFnPolyTy _compiled _schema _fnName _) -> do
                                    cataId <- tyFixerFnId
                                    handlerTypes <- traverse unsafeRefType (Vector.toList handlers)
                                    scrutTy <- unsafeRefType arg
                                    let cataFnConcrete = applyArgs cataFnPolyTy (scrutTy : handlerTypes)
                                        newValNode = AppInternal (forgetExtendedId i) (Vector.cons arg handlers) Vector.empty cataFnConcrete
                                        newASGNode = AValNode valT newValNode
                                    insertAndMarkVisited i newASGNode
                                    -- NOTE: This is just a placeholder tagged with the polymorphic function type, which we need.
                                    --       The body is a reference to a single error node that we track and will ignore/remove.
                                    --       TODO: There's only one of these for each type so add a check to save us work if we already did it
                                    syntheticCataFnNode <- conjureFunction cataFnPolyTy
                                    insertAndMarkVisited cataId syntheticCataFnNode
                        Match scrut handlers -> do
                            traverse_ goRef handlers
                            goRef scrut
                            matchId <- tyFixerFnId
                            scrutTy <- unsafeRefType scrut
                            handlerTypes <- traverse unsafeRefType $ Vector.toList handlers
                            let tn = unsafeDatatypeName scrutTy
                            tyFixers <- gets (R..! #tyFixerData)
                            case matchData =<< M.lookup tn tyFixers of
                                Nothing ->
                                    error $
                                        "Fatal Error: No type fixer function data for pattern matches on " <> show tn
                                Just (TyFixerFnData _nm _enc matchFnPolyTy _compiled _schema _fnName _) -> do
                                    let matchFnConcrete = applyArgs matchFnPolyTy (scrutTy : handlerTypes)
                                        newValNode = AppInternal (forgetExtendedId i) (Vector.cons scrut handlers) Vector.empty matchFnConcrete
                                        newASGNode = AValNode valT newValNode
                                    insertAndMarkVisited i newASGNode
                                    -- NOTE: See previous note
                                    syntheticMatchFnNode <- conjureFunction matchFnPolyTy
                                    insertAndMarkVisited matchId syntheticMatchFnNode
                        DataConstructor tn ctorName ctorArgs -> do
                            traverse_ goRef ctorArgs
                            argTys <- traverse unsafeRefType $ Vector.toList ctorArgs
                            tyFixers <- gets (R..! #tyFixerData)
                            case introData <$> M.lookup tn tyFixers of
                                Nothing ->
                                    error $
                                        "Fatal Error: No type fixer function data for datatype introductions for type " <> show tn
                                Just constrFunctions ->
                                    resolveCtorIx tn ctorName >>= \case
                                        Nothing -> error $ "Fatal Error: No data for constructor " <> show ctorName <> " found in type " <> show tn
                                        Just ctorIx -> do
                                            ctorFnId <- tyFixerFnId
                                            let ctorFnData = constrFunctions Vector.! ctorIx
                                                TyFixerFnData _nm _enc ctorFnPolyTy _compiled _schema _fnName _ = ctorFnData
                                                ctorFnConcrete = applyArgs ctorFnPolyTy argTys
                                                newValNode = AppInternal (forgetExtendedId i) ctorArgs Vector.empty ctorFnConcrete
                                                newASGNode = AValNode valT newValNode
                                            insertAndMarkVisited i newASGNode
                                            -- NOTE: See previous note
                                            syntheticCtorFnNode <- conjureFunction ctorFnPolyTy
                                            insertAndMarkVisited ctorFnId syntheticCtorFnNode
      where
        goRef :: Ref -> MetaM TransformState ()
        goRef = \case
            AnId child -> resolveExtended child >>= go
            AnArg{} -> pure ()

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
            if a `Set.member` allOriginalVars
                then pure $ Set.singleton a
                else pure Set.empty
        BuiltinFlat{} -> pure Set.empty
        ThunkT (CompN _ (ArgsAndResult thunkArgs thunkRes)) -> local (+ 1) $ do
            let toTraverse = Vector.toList $ Vector.snoc thunkArgs thunkRes
            Set.unions <$> traverse collectLocalVars toTraverse
        Datatype _ dtArgs -> Set.unions <$> traverse collectLocalVars (Vector.toList dtArgs)

-- Misc utils

retTy :: CompT a -> ValT a
retTy (CompN _ (ArgsAndResult _ res)) = res

intT :: ValT AbstractTy
intT = BuiltinFlat IntegerT

byteStringT :: ValT AbstractTy
byteStringT = BuiltinFlat ByteStringT

syntheticLamNode :: UniqueError -> CompT AbstractTy -> ASGNode
syntheticLamNode (UniqueError errId) funTy = ACompNode funTy (LamInternal (AnId errId))
