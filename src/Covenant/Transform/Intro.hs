module Covenant.Transform.Intro where

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Covenant.Type (
    AbstractTy,
    CompT (CompN),
    CompTBody (ArgsAndResult),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName,
    ValT (Datatype),
 )

import Covenant.Data (DatatypeInfo)
import Covenant.Index (Count)
import Covenant.MockPlutus (
    PlutusTerm,
    constrData,
    listData,
    pApp,
    pConstr,
    pLam,
    pVar,
    plutus_ConstrData,
    plutus_I,
 )
import Data.Foldable (
    foldl',
 )
import Optics.Core (view)

import Covenant.Transform.Common

-- TODO: Better comments (tho fortunately this one is the most straightforward)

mkConstructorFunctions :: TyName -> AppTransformM (Vector TyFixerFnData)
mkConstructorFunctions tn =
    lookupDatatypeInfo tn >>= \dtInfo -> case view #originalDecl dtInfo of
        DataDeclaration _tn cnt ctors enc -> do
            Vector.ifoldM (go dtInfo cnt enc) Vector.empty ctors
        OpaqueData{} -> error "TODO: intro forms for opaque"
  where
    go ::
        DatatypeInfo AbstractTy ->
        Count "tyvar" ->
        DataEncoding ->
        Vector TyFixerFnData ->
        Int ->
        Constructor AbstractTy ->
        AppTransformM (Vector TyFixerFnData)
    go _dtInfo cnt enc acc cIx (Constructor (ConstructorName cName) argTys) = do
        let ctorFnTy = mkCtorFnTy cnt argTys
            schema = mkTypeSchema enc ctorFnTy
            funName = cName
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
        pure $ Vector.snoc acc here
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
                DataSchema _ handlerArgPosDict -> do
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
                                pure $ plutus_ConstrData (fromIntegral ctorIx) handledCtorArgs
                            NewtypeData ->
                                -- NOTE: Double check whether we need to do any embedding here. Koz thinks we don't and he's pretty
                                --       confident, so we probably don't.
                                pure $ handledCtorArgs Vector.! 0

        mkCtorFnTy :: Count "tyvar" -> Vector (ValT AbstractTy) -> CompT AbstractTy
        mkCtorFnTy datatypeNumParams args =
            let result = Datatype tn (countToTyVars datatypeNumParams)
             in CompN datatypeNumParams (ArgsAndResult args result)
