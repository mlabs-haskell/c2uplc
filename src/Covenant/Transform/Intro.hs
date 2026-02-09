{-# LANGUAGE OverloadedLists #-}

module Covenant.Transform.Intro
  ( mkConstructorFunctions,
  )
where

import Control.Monad.RWS.Strict (MonadReader, MonadState)
import Covenant.CodeGen.Stubs (MonadStub)
import Covenant.Data (DatatypeInfo)
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (Count, ix0, ix1)
import Covenant.Plutus
  ( listData,
    pApp,
    pConstr,
    pDelay,
    pLam,
    pVar,
    plutus_ConstrData,
    plutus_I,
  )
import Covenant.Transform.Common
  ( BuiltinFnData
      ( Data_B,
        Data_Constr,
        Data_I,
        Data_List,
        Data_Map,
        List_Cons,
        List_Nil,
        Map_Map,
        Pair_Pair
      ),
    TyFixerFnData
      ( BuiltinTyFixer,
        TyFixerFnData,
        mfCompiled,
        mfEncoding,
        mfFunName,
        mfNodeKind,
        mfPolyType,
        mfTyName,
        mfTypeSchema
      ),
    TyFixerNodeKind (IntroNode),
    countToTyVars,
    genLambdaArgNames,
  )
import Covenant.Transform.Pipeline.Common
  ( lookupDatatypeInfo,
    resolvePolyRepHandler,
  )
import Covenant.Transform.Pipeline.Monad
  ( Datatypes,
    RepPolyHandlers,
  )
import Covenant.Transform.Schema
  ( TypeSchema (DataSchema, SOPSchema),
    mkTypeSchema,
  )
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp1, Comp2, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (BuiltinFlat, Datatype),
    tyvar,
  )
import Data.Foldable
  ( foldl',
  )
import Data.Kind (Type)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Optics.Core (view)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term)

-- TODO: Better comments (tho fortunately this one is the most straightforward)

mkConstructorFunctions ::
  forall (m :: Type -> Type).
  ( MonadStub m,
    MonadReader Datatypes m,
    MonadState RepPolyHandlers m
  ) =>
  TyName ->
  m (Vector TyFixerFnData)
mkConstructorFunctions tn =
  lookupDatatypeInfo tn >>= \dtInfo -> case view #originalDecl dtInfo of
    DataDeclaration _tn cnt ctors enc -> do
      Vector.ifoldM (go dtInfo cnt enc) Vector.empty ctors
    OpaqueData _ _ -> error "TODO: intro forms for opaque"
  where
    go ::
      DatatypeInfo AbstractTy ->
      Count "tyvar" ->
      DataEncoding ->
      Vector TyFixerFnData ->
      Int ->
      Constructor AbstractTy ->
      m (Vector TyFixerFnData)
    go _ _ enc@(BuiltinStrategy _) acc _ (Constructor (ConstructorName cName) _) = do
      here <- builtinIntroForm enc tn cName
      pure $ Vector.snoc acc here
    go _dtInfo cnt enc acc cIx (Constructor (ConstructorName cName) argTys) = do
      let ctorFnTy = mkCtorFnTy cnt argTys
          schema = mkTypeSchema True enc ctorFnTy
          funName = cName
      compiled <- genIntroFormPLC enc schema cIx
      let here =
            TyFixerFnData
              { mfTyName = tn,
                mfEncoding = enc,
                mfPolyType = ctorFnTy,
                mfCompiled = compiled,
                mfTypeSchema = schema,
                mfFunName = funName,
                mfNodeKind = IntroNode
              }
      pure $ Vector.snoc acc here
      where
        genIntroFormPLC ::
          DataEncoding ->
          TypeSchema ->
          Int ->
          m (Term Name DefaultUni DefaultFun ())
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
              lamArgVars = pVar <$> names
              nameTyPairs = Vector.zip ctorArgNames ctorArgs
              lamBuilder = foldl' (\g argN -> g . pLam argN) id names . pDelay
          case schema of
            SOPSchema _ -> pure . lamBuilder $ pConstr (fromIntegral ctorIx) (pVar <$> ctorArgNames)
            DataSchema _ handlerArgPosDict -> do
              {- We need to resolve embeddings for both type variables *and* statically known concrete builtin types.
              -}
              let resolveEmbedding :: ValT AbstractTy -> m (Maybe (Term Name DefaultUni DefaultFun ()))
                  resolveEmbedding = resolvePolyRepHandler IntroNode handlerArgPosDict lamArgVars Nothing
              handledCtorArgs <- Vector.forM nameTyPairs $ \(cArgNm, cArgTy) ->
                resolveEmbedding cArgTy >>= \case
                  Nothing -> do
                    let res = pVar cArgNm
                    pure res
                  Just argHandler -> do
                    let res = pApp argHandler (pVar cArgNm)
                    pure res
              case dataEnc of
                -- TODO: Fill in some of the helpers (plutus_I, listData, etc) and make sure you use the "right version" here
                SOP -> error "something went horribly wrong, DataSchema w/ SOP encoding"
                BuiltinStrategy _ -> error "TODO: Remember how to handle code generation for builtin strategies"
                PlutusData strat -> case strat of
                  EnumData -> pure $ lamBuilder (plutus_I $ fromIntegral ctorIx)
                  ProductListData -> pure . lamBuilder $ listData handledCtorArgs
                  ConstrData ->
                    pure . lamBuilder $ plutus_ConstrData (fromIntegral ctorIx) handledCtorArgs
                  NewtypeData ->
                    -- NOTE: Double check whether we need to do any embedding here. Koz thinks we don't and he's pretty
                    --       confident, so we probably don't.
                    pure . lamBuilder $ handledCtorArgs Vector.! 0

        -- TODO/FIXME: Make sure that this returns a THUNK type
        mkCtorFnTy :: Count "tyvar" -> Vector (ValT AbstractTy) -> CompT AbstractTy
        mkCtorFnTy datatypeNumParams args =
          let result = Datatype tn (countToTyVars datatypeNumParams)
           in CompN datatypeNumParams (ArgsAndResult args result)

-- TODO: This should take a constructor of Covenant.Internal.Strategy.InternalStrategy
--       but we don't export that (I presume Koz thought "internal" meant "to the main repo
--       when it really means "to the compiler")
--       \/ \/ \/ Important \/ \/ \/
-- NOTE: The CompT arg to BuiltinTyFixer is the "public" type. We'll just handle the "private" type
--       manually during the resolve poly rep step.
builtinIntroForm ::
  forall (m :: Type -> Type).
  ( MonadStub m,
    MonadReader Datatypes m,
    MonadState RepPolyHandlers m
  ) =>
  DataEncoding -> -- only need the encoding arg b/c main repo doesn't export right stuff
  TyName ->
  Text ->
  m TyFixerFnData
builtinIntroForm _ (TyName tn) ctorNm = case tn of
  "List" -> case ctorNm of
    "Cons" -> do
      -- Does not need a projection (I am pretty sure)
      let consTy = Comp1 $ a :--:> listT a :--:> ReturnT (listT a)
      pure $ BuiltinTyFixer consTy List_Cons
    "Nil" -> do
      -- Hopefully this doesn't break anything!
      let nilTy = Comp1 $ ReturnT (listT a)
      pure $ BuiltinTyFixer nilTy List_Nil
    _ -> unsupported
  "Data" -> case ctorNm of
    "I" -> mkDataIntro intT Data_I
    "B" -> mkDataIntro byteStringT Data_B
    "Map" -> mkDataIntro (listT (pairT dataT dataT)) Data_Map
    "List" -> mkDataIntro (listT dataT) Data_List
    "Constr" ->
      pure
        . BuiltinTyFixer
          (Comp0 $ intT :--:> listT dataT :--:> ReturnT dataT)
        $ Data_Constr
    _ -> unsupported
  "Map" -> case ctorNm of
    "Map" -> pure $ BuiltinTyFixer mapIntroSig Map_Map
    _ -> unsupported
  "Pair" -> case ctorNm of
    "Pair" -> pure $ BuiltinTyFixer pairIntroSig Pair_Pair
    _ -> unsupported
  _ -> error $ T.unpack tn <> " is not a supported type fixer for any internal encoding strategy"
  where
    unsupported :: forall a. m a
    unsupported = error $ T.unpack ctorNm <> " is not a valid constructor of " <> T.unpack tn

    mapIntroSig :: CompT AbstractTy
    mapIntroSig = Comp2 $ listT (pairT a b) :--:> ReturnT (mapT a b)

    pairIntroSig :: CompT AbstractTy
    pairIntroSig = Comp2 $ a :--:> b :--:> ReturnT (pairT a b)

    mkDataIntro :: ValT AbstractTy -> BuiltinFnData -> m TyFixerFnData
    mkDataIntro t dat = pure $ BuiltinTyFixer (Comp0 $ t :--:> ReturnT dataT) dat

    dataT :: ValT AbstractTy
    dataT = dt "Data" []

    listT :: ValT AbstractTy -> ValT AbstractTy
    listT t = dt "List" [t]

    pairT :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
    pairT x y = dt "Pair" [x, y]

    -- The ADT not the ctor of data
    mapT :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
    mapT k v = dt "Map" [k, v]

    intT = BuiltinFlat IntegerT
    byteStringT = BuiltinFlat ByteStringT

    a = tyvar Z ix0
    b = tyvar Z ix1

    dt = Datatype
