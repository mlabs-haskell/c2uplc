module Covenant.Transform.Intro where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, asks, execRWS, local, modify)

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
import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT,
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar,
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (MonadReader, Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), StateT)
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
import Covenant.Test (Id (UnsafeMkId))
import Data.Foldable (
    find,
    foldl',
    traverse_,
 )
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, preview, review, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

import Covenant.Transform.Common

-- TODO: Better comments (tho fortunately this one is the most straightforward)

mkConstructorFunctions :: TyName -> AppTransformM (Map Id TyFixerFnData)
mkConstructorFunctions tn =
    lookupDatatypeInfo tn >>= \dtInfo -> case view #originalDecl dtInfo of
        DataDeclaration tn cnt ctors enc -> do
            Vector.ifoldM (go dtInfo cnt enc) M.empty ctors
        OpaqueData{} -> error "TODO: intro forms for opaque"
  where
    go ::
        DatatypeInfo AbstractTy ->
        Count "tyvar" ->
        DataEncoding ->
        Map Id TyFixerFnData ->
        Int ->
        Constructor AbstractTy ->
        AppTransformM (Map Id TyFixerFnData)
    go dtInfo cnt enc acc cIx (Constructor (ConstructorName cName) argTys) = do
        let ctorFnTy = mkCtorFnTy cnt argTys
            schema = mkTypeSchema enc ctorFnTy
            funName = cName
        newId <- nextId
        compiled <- genIntroFormPLC enc schema cIx
        let here =
                TyFixerFnData
                    { mfTyName = tn
                    , mfEncoding = enc
                    , mfPolyType = ctorFnTy
                    , mfCompiled = compiled
                    , mfTypeSchema = schema
                    , mfFunName = funName
                    , mfNodeKind = IntroNode
                    }
        pure $ M.insert newId here acc
      where
        genIntroFormPLC ::
            DataEncoding ->
            TypeSchema ->
            Int ->
            AppTransformM PlutusTerm
        genIntroFormPLC dataEnc schema ctorIx = do
            let introFnArgs = case schema of
                    SOPSchema (CompN _ (ArgsAndResult args _)) -> args
                    DataSchema (CompN _ (ArgsAndResult args _)) _ -> args
                -- these are the ARGUMENTS TO THE CONSTRUCTOR
                ctorArgs = argTys
            -- These are the NAMES OF ALL THE ARGUMENTS TO THE INTRO FUNCTION. In this branch
            -- this will (almost always) contain MORE NAMES than the args to the constructor
            names <- genLambdaArgNames cName introFnArgs
            -- The names of arguments to the ctors
            let ctorArgNames = Vector.take (Vector.length ctorArgs) names
                lamArgVars = pVar <$> ctorArgNames
                nameTyPairs = Vector.zip ctorArgNames ctorArgs
                lamBuilder = foldl' (\g argN -> g . pLam argN) id names
            case schema of
                SOPSchema _ -> pure . lamBuilder $ pConstr (fromIntegral ctorIx) (pVar <$> ctorArgNames)
                DataSchema (CompN _ (ArgsAndResult introFnArgs _)) handlerArgPosDict -> do
                    {- We need to resolve embeddings for both type variables *and* statically known concrete builtin types.
                    -}
                    let resolveEmbedding :: ValT AbstractTy -> AppTransformM (Maybe PlutusTerm)
                        resolveEmbedding = resolvePolyRepHandler IntroNode handlerArgPosDict lamArgVars Nothing
                    handledCtorArgs <- Vector.forM nameTyPairs $ \(cArgNm, cArgTy) ->
                        resolveEmbedding cArgTy >>= \case
                            Nothing -> pure $ pVar cArgNm
                            Just argHandler -> pure $ pApp argHandler (pVar cArgNm)
                    case dataEnc of
                        -- TODO: Fill in some of the helpers (plutus_I, listData, etc) and make sure you use the "right version" here
                        SOP -> error "something went horribly wrong, DataSchema w/ SOP encoding"
                        BuiltinStrategy _ -> error "TODO: Remember how to handle code generation for builtin strategies"
                        PlutusData strat -> case strat of
                            EnumData -> pure $ lamBuilder (plutus_I $ fromIntegral ctorIx)
                            ProductListData -> pure $ listData handledCtorArgs
                            ConstrData ->
                                -- LIVE AS OF 12/31
                                -- NOTE/FIXME/TODO: This shouldn't be plutus_I, use ConstrData which takes an Integer not a data
                                pure $ constrData (plutus_I $ fromIntegral ctorIx) (listData handledCtorArgs)
                            NewtypeData ->
                                -- NOTE: Double check whether we need to do any embedding here. Koz thinks we don't and he's pretty
                                --       confident, so we probably don't.
                                pure $ handledCtorArgs Vector.! 0

        mkCtorFnTy :: Count "tyvar" -> Vector (ValT AbstractTy) -> CompT AbstractTy
        mkCtorFnTy datatypeNumParams args =
            let result = Datatype tn (countToTyVars datatypeNumParams)
             in CompN datatypeNumParams (ArgsAndResult args result)
