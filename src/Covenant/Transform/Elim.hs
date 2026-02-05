{-# LANGUAGE OverloadedLists #-}

module Covenant.Transform.Elim where

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Covenant.Type (
    AbstractTy,
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp1, Comp2, Comp3, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (BuiltinFlat, Datatype, ThunkT),
    tyvar,
 )

import Control.Monad.Except (runExceptT)
import Covenant.Data (DatatypeInfo (DatatypeInfo), mkMatchFunTy)
import Covenant.MockPlutus (
    PlutusTerm,
    pApp,
    pCase,
    pForce,
    pLam,
    pVar,
    ppTerm,
    unIData,
    unListData,
 )
import Data.Foldable (
    foldl',
 )
import Data.Text (Text)
import Data.Text qualified as T
import Optics.Core (view)

import Control.Monad.RWS.Strict (MonadReader, MonadState)
import Covenant.ArgDict (pName, pValT, pValTs, pVec)
import Covenant.CodeGen.Stubs (MonadStub)
import Covenant.DeBruijn
import Covenant.Index
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Covenant.Transform.Pipeline.Monad
import Data.Kind (Type)
import Data.Map.Strict (Map)

-- import Debug.Trace (traceM)
import UntypedPlutusCore ()

{- NOTE: The type of the "function part" is just going to be the BBF (plus unwrappers),
         since we always apply the scrutinee and handler functions "all at once" with the
         match nodes we are transforming, and will therefore be able to concretify
         any type variables occuring in the fully polymorphic function type.

         So the type of the function for a SOP encoded `Maybe` would be:

         `forall a r. Maybe a -> r -> (a -> r) -> r`

         And for a data encoded maybe, it should ("eventually") be

         `forall a r. Maybe a -> r -> (a -> r) -> (r -> r) -> r`

         Though we are going to use the same "trick" here that we do for introduction, that is:
           - For our first pass, we will replace `match` nodes with a dummy function with
             no wrapper/unwrapper handlers
           - We will codegen a suitable function that *does* make use of handlers, and record that
             type seperately
           - *After* we use the "initial" ASG to fully concretify the types, we will do another pass
             where we will explicitly introduce the handlers as extra arguments to the function and
             apply the needed handler arguments.

         The reason for doing things this way is that for our concretification analysis pass, we only really
         care about ensuring that all type variables are fully concretified (or concretified as far as possible).
         We need to know that to handle representational polymorphism. The "transform every type fixer into an app node"
         this is intended to make the analysis much easier (which it does), but we need to complete that analysis
         before we can determine *which* wrapper/unwrapper handlers the expanded function needs to be applied to.

         This is admittedly a bit strange, however I do not think there is an easier way to do things.

-}

-- The ONLY case where we should end up with Nothing is something isomorphic to Void
mkDestructorFunction ::
    forall (m :: Type -> Type).
    ( MonadStub m
    , MonadReader Datatypes m
    , MonadState RepPolyHandlers m
    ) =>
    TyName ->
    m (Maybe TyFixerFnData)
mkDestructorFunction tn@(TyName tyNameInner) = lookupDatatypeInfo tn >>= go
  where
    go :: DatatypeInfo AbstractTy -> m (Maybe TyFixerFnData)
    go (DatatypeInfo OpaqueData{} _ _ _) = error "TODO Opaque eliminators"
    go (DatatypeInfo (DataDeclaration _ _ _ enc@(BuiltinStrategy _)) _ _ _) = Just <$> builtinElimForm tn enc
    go dtInfo = do
        let ogDecl = view #originalDecl dtInfo
        case runExceptT (mkMatchFunTy ogDecl) of
            -- "Nothing" here means "Datatype is isomorphic to `Void`"
            Nothing -> pure Nothing
            Just eRes -> case eRes of
                Left bbfErr ->
                    error $
                        "Error: Could not create destructor function. Invalid datatype. BBF Error: "
                            <> show bbfErr
                Right matchFunTy -> do
                    let enc = view #datatypeEncoding ogDecl
                    let schema = mkTypeSchema False enc matchFunTy
                    let matchFunName = "match_" <> tyNameInner
                    compiled <- genElimFormPLC matchFunTy matchFunName enc schema
                    let here =
                            TyFixerFnData
                                { mfTyName = tn
                                , mfEncoding = enc
                                , mfPolyType = matchFunTy
                                , mfCompiled = compiled
                                , mfTypeSchema = schema
                                , mfFunName = matchFunName
                                , mfNodeKind = MatchNode
                                }
                    pure . Just $ here
    {- IMPORTANT NOTE: While *here* we are working with a generated match function with branch handler
                       arguments that will NOT be thunked for nullary constructors (i.e. the type of a
                       Nothing handler HERE is `r` and not `ThunkT (ReturnT r)`), we have to REMEMBER TO
                       BE VERY CAREFUL TO DE-THUNK NULLARY CTOR HANDLERS WHEN WE ACTUALLY APPLY THE FUNCTION TYPES.

                       If our match node was constructed with the `match` helper, then handlers for nullary ctors
                       WILL be thunks and that WILL break things if we don't catch it.
    -}
    genElimFormPLC :: -- This is the "no handlers added" type, which is useful for us when SOP or Constr things
        CompT AbstractTy ->
        Text ->
        DataEncoding ->
        TypeSchema ->
        m PlutusTerm
    genElimFormPLC (CompN _ (ArgsAndResult origMatchFnArgs _)) nameBase enc schema = do
        -- These are the FULL arguments to the function (not the synthetic type we use for analysis),
        -- and this comes from the schema generator. This type includes projection/embedding functions, the
        --- original type does not.
        let matchFnArgs = schemaFnArgs schema
        -- These are the (PLC) names of all of the arguments to the match function.
        -- E.g. for maybe they will be references to [Maybe a, r, (a -> r)]
        lamArgNames <- genLambdaArgNames nameBase matchFnArgs
        let lamArgVars = pVar <$> lamArgNames
            -- This is a function that takes a PLC lambda body for the match function and
            -- and returns a PLC lambda.
            lamBuilder :: PlutusTerm -> PlutusTerm
            lamBuilder = foldl' (\g argN -> g . pLam argN) id lamArgNames
            {- NOTE: It's important to keep in mind here that for an arbitrary ADT, the
                     generated match function has a regular structure: The scrutinee comes first, then
                     all of the branch handlers. Because each term var bound by the lambda corresponds to a type
                     arg, we can use this to derive references to each branch handler directly.
            -}
            scrutinee :: PlutusTerm
            scrutinee = pVar $ lamArgNames Vector.! 0

            -- We ignore the "extra unwrapper args" here because we're trying to get the names of the handlers for each
            -- match arm (and we have another way of looking up the unwrappers when we need to)
            rawBranchHandlers :: Vector PlutusTerm
            rawBranchHandlers =
                let numHandlers = Vector.length origMatchFnArgs - 1
                 in pVar <$> Vector.slice 1 numHandlers lamArgNames

            -- inserts forces if the types say we need them
            insertForce :: (ValT AbstractTy, PlutusTerm) -> (ValT AbstractTy, PlutusTerm)
            insertForce (v, t) = case v of
                ThunkT{} -> (v, pForce t)
                _ -> (v, t)
            typedBranchHandlers :: Vector (ValT AbstractTy, PlutusTerm)
            typedBranchHandlers = insertForce <$> Vector.zip (Vector.drop 1 origMatchFnArgs) rawBranchHandlers

            (_, branchHandlers) = Vector.unzip typedBranchHandlers
        traceM $
            "genElimPLC:\n  matchFnArgs: "
                <> pVec pValT matchFnArgs
                <> "\n  lamArgNames: "
                <> pVec pName lamArgNames
                <> "\n branchHandlers: "
                <> pVec ppTerm rawBranchHandlers
        case schema of
            SOPSchema _ ->
                {- This is the easiest one. We do the only thing we could possibly do.
                -}
                pure . lamBuilder $ pCase scrutinee branchHandlers
            DataSchema _ handlerArgPosDict -> do
                -- This lets us look up the name (i.e. the var bound by our lambda) which corresponds to the
                -- projection/embedding function we need to use for a particular value with a bare tyvar type
                let resolveUnwrapper :: ValT AbstractTy -> m (Maybe PlutusTerm)
                    resolveUnwrapper = resolvePolyRepHandler MatchNode handlerArgPosDict lamArgVars Nothing

                case enc of
                    SOP -> error $ "Data schema for SOP encoding when compiling match functions for " <> T.unpack tyNameInner
                    BuiltinStrategy _ -> error "TODO: Implement match fn codegen for builtin types"
                    PlutusData strat -> case strat of
                        EnumData ->
                            {- We know the scrutinee is an Int (or really a data-wrapped I 3, I think?).

                               We also know that the range of values it can take is "suitably compact", i.e., starts at 0
                               and increments by one for each additional enum constructor.

                               Because this is an enumeration, there are no arguments. All of the arm/branch handlers do not take any arguments,
                               and we don't need to do any unwrapping.

                               So this should be really straightforward. The body is just a case expression over the unwrapped (I Integer) where each
                               match arm is just some arm/branch handler argument to the function.
                            -}
                            pure . lamBuilder $ pCase (unIData scrutinee) branchHandlers
                        ProductListData ->
                            case origMatchFnArgs Vector.!? 1 of
                                Nothing ->
                                    error $
                                        "CodeGen failure while generating PLC match function for type "
                                            <> T.unpack tyNameInner
                                            <> ": No handler for single ProductListData ctor"
                                Just thisBranchHandler -> do
                                    traceM $ "\n  thisBranchHandlerTy: " <> show thisBranchHandler
                                    case thisBranchHandler of
                                        -- In the generated match function we do not ever construct a (ThunkT (ReturnT v))
                                        -- value, so we should be able to ignore the possibility.
                                        ThunkT (CompN _ (ArgsAndResult thisBranchHandlerArgTys _)) -> do
                                            listEliminator <-
                                                genFiniteListEliminator
                                                    (lamArgVars Vector.! 1)
                                                    (unListData scrutinee)
                                                    resolveUnwrapper
                                                    (Vector.toList thisBranchHandlerArgTys)
                                            pure . lamBuilder $ listEliminator
                                        _ ->
                                            -- Anything else means we have a nullary constructor and can bypass any hard work here
                                            pure . lamBuilder $ branchHandlers Vector.! 1
                        ConstrData -> do
                            {- See comments on `pCaseConstrData` in Covenant.Transform.Common for an explanation
                               of exactly how this works. The general idea is that we use casing on the constructor index
                               integer to get better performance than we would get with builtins.
                            -}
                            caseBody <- pCaseConstrData scrutinee typedBranchHandlers resolveUnwrapper
                            pure . lamBuilder $ caseBody
                        NewtypeData -> do
                            {- This is trivial-ish. We just need to check whether the single arg to the single branch handler
                               (which is what the type of the scrutinee "really is" if it's newtype encoded) needs a projection, and if so, we

                              -- NOTE/FIXME: (STILL LIVE 12/30) WE DO NOT NEED TO DO EMBEDDINGS OR PROJECTIONS HERE
                            -}
                            let thisBranchHandlerTerm = branchHandlers Vector.! 0
                                realScrutTy = case origMatchFnArgs Vector.! 1 of
                                    ThunkT (CompN _ (ArgsAndResult args _)) -> args Vector.! 0
                                    _ -> error $ T.unpack tyNameInner <> " has a newtype encoding, is not a valid newtype"
                            resolveUnwrapper realScrutTy >>= \case
                                Nothing -> pure . lamBuilder $ pApp thisBranchHandlerTerm scrutinee
                                Just projFn -> pure . lamBuilder $ pApp thisBranchHandlerTerm (pApp projFn scrutinee)

-- as with intro forms, covenant doesn't export some stuff we need and i'm in a huge rush
-- eventually we should dispatch on the DataEncoding not the TyName (but this will work for now)
-- NOTE: As with the intro functions, these are the "public" function types and we will handle
--       conjuring the "real" function types for the underlying PLC during the rep poly resolution pass
builtinElimForm ::
    forall (m :: Type -> Type).
    ( MonadStub m
    , MonadReader Datatypes m
    , MonadState RepPolyHandlers m
    ) =>
    TyName ->
    DataEncoding ->
    m TyFixerFnData
builtinElimForm (TyName tn) _enc = case tn of
    "List" -> do
        let matchListTy =
                Comp2 $
                    listT a
                        :--:> b
                        :--:> thunk0 (a' :--:> listT a' :--:> ReturnT b')
                        :--:> ReturnT b
        pure $ BuiltinTyFixer matchListTy List_Match
    "Pair" -> do
        let matchPairTy =
                Comp3 $
                    pairT a b
                        :--:> thunk0 (a' :--:> b' :--:> ReturnT c')
                        :--:> ReturnT c
        pure $ BuiltinTyFixer matchPairTy Pair_Match
    "Map" -> do
        let matchMapTy =
                Comp3 $
                    mapT a b
                        :--:> thunk0 (listT (pairT a' b') :--:> ReturnT c')
                        :--:> ReturnT c'
        pure $ BuiltinTyFixer matchMapTy Map_Match
    "Data" -> do
        let matchDataTy =
                Comp1 $
                    dataT
                        :--:> thunk0 (intT :--:> listT dataT :--:> ReturnT a')
                        :--:> thunk0 (listT (pairT dataT dataT) :--:> ReturnT a')
                        :--:> thunk0 (listT dataT :--:> ReturnT a')
                        :--:> thunk0 (intT :--:> ReturnT a')
                        :--:> thunk0 (byteStringT :--:> ReturnT a')
                        :--:> ReturnT a'
        pure $ BuiltinTyFixer matchDataTy Data_Match
    _ -> error $ "builtin elimination forms not supported for type: " <> T.unpack tn
  where
    thunk0 = ThunkT . Comp0

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
    c = tyvar Z ix2

    a' = tyvar (S Z) ix0
    b' = tyvar (S Z) ix1
    c' = tyvar (S Z) ix2

    dt = Datatype
