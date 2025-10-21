module Covenant.CodeGen (generatePLC) where

import Covenant.ASG (
    ASGNode (ACompNode, AValNode, AnError),
    Arg (UnArg),
    CompNodeInfo (Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
 )
import Covenant.Constant (AConstant)
import Covenant.Data (DatatypeInfo)
import Covenant.Type (
    AbstractTy,
    CompT,
    Constructor,
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (
        EnumData,
        NewtypeData,
        ProductListData
    ),
    TyName,
 )

-- N.B. *WE* have two different things called `ConstrData`
import Covenant.Type qualified as T

import Control.Monad.Error.Class (MonadError, throwError)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.RWS (RWS)

import Data.Foldable (foldl')

import Data.Kind (Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Data.Text (Text)

import Optics.Core (review, view)

import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (intIndex)
import Covenant.MockPlutus (
    PlutusTerm,
    SomeBuiltin (SomeBuiltin1, SomeBuiltin2, SomeBuiltin3, SomeBuiltin6),
    bData,
    constrData,
    iData,
    idName,
    listData,
    mapData,
    pApp,
    pBuiltin,
    pConstr,
    pDataList,
    pError,
    pLam,
    pVar,
    plutus_ConstrData,
    plutus_I,
 )

import Covenant.ArgDict (idToName)

import PlutusCore (Name)

data CodeGenError
    = NoASG
    | TermNotInContext Id
    | NoDatatype TyName
    | ConstructorNotInDatatype TyName ConstructorName
    | InvalidOpaqueEncoding Text
    | ArgResolutionFail ArgResolutionFailReason
    deriving stock (Show, Eq)

data ArgResolutionFailReason
    = {- | We got @Nothing@ when we tried to look up the context corresponding to the
      @Id@ of the parent node where the arg was found.
      -}
      ParentIdLookupFailed Id
    | {- | The @Id@ of the parent node of the arg we are examining should index a @Vector Id@ but instead
      indexes a @Vector Name@.
      -}
      ParentIdPointsAtNames Id
    | -- | The @DeBruijn@ index of the arg points to an out of bounds lambda.
      DBIndexOutOfBounds DeBruijn
    | {- | The @Id@ of the lambda corresponding to the @DeBruijn@ index does not correspond to anything in our
      argument resolution dictionary.
      -}
      NoBindingContext Id
    | {- | The @Id@ of the Lambda that the DeBruijn points at corresponds to an entry in our
      argument resolution diciontary, but that entry is a @Vector Id@ and not the @Vector Name@
      that we need
      -}
      LamIdPointsAtContext Id
    deriving stock (Show, Eq)

newtype CodeGenM a = CodeGenM (ExceptT CodeGenError (RWS (Map TyName (DatatypeInfo AbstractTy)) () (Map Id PlutusTerm)) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadReader (Map TyName (DatatypeInfo AbstractTy))
        , MonadState (Map Id PlutusTerm)
        , MonadError CodeGenError
        )
        via (ExceptT CodeGenError (RWS (Map TyName (DatatypeInfo AbstractTy)) () (Map Id PlutusTerm)))

lookupTerm :: Id -> CodeGenM PlutusTerm
lookupTerm i =
    gets (M.lookup i) >>= \case
        Nothing -> throwError $ TermNotInContext i
        Just term -> pure term

lookupDatatype :: TyName -> CodeGenM (DatatypeInfo AbstractTy)
lookupDatatype tn =
    asks (M.lookup tn) >>= \case
        Nothing -> throwError $ NoDatatype tn
        Just info -> pure info

generatePLC ::
    Map Id (Either (Vector Name) (Vector Id)) ->
    [(Id, ASGNode)] ->
    CodeGenM PlutusTerm
generatePLC argDict = \case
    [] -> throwError NoASG
    ((i, n) : rest) -> go i n rest
  where
    go :: Id -> ASGNode -> [(Id, ASGNode)] -> CodeGenM PlutusTerm
    go i node rest = case rest of
        [] -> nodeToTerm i argDict node
        ((i', node') : rest') -> do
            let letBindable = countOccurs i (node : map snd rest) > 1
            thisTerm <- nodeToTerm i argDict node
            if letBindable
                then do
                    modify $ M.insert i thisTerm
                    go i' node' rest'
                else do
                    let iName = idName i
                    let iVar = pVar iName
                    modify $ M.insert i iVar
                    termInner <- go i' node' rest'
                    pure $ pLam iName termInner `pApp` thisTerm

nodeToTerm ::
    Id -> -- The Id of *THIS* node. Needed for arg resolution
    Map Id (Either (Vector Name) (Vector Id)) ->
    ASGNode ->
    CodeGenM PlutusTerm
nodeToTerm i argDict = \case
    ACompNode compTy compNodeInfo -> case compNodeInfo of
        Builtin1 bi1 -> pure $ pBuiltin (SomeBuiltin1 bi1)
        Builtin2 bi2 -> pure $ pBuiltin (SomeBuiltin2 bi2)
        Builtin3 bi3 -> pure $ pBuiltin (SomeBuiltin3 bi3)
        Builtin6 bi6 -> pure $ pBuiltin (SomeBuiltin6 bi6)
        Force r -> forceToTerm r
        Lam r -> lamToTerm compTy r
    AValNode _valT valNodeInfo -> case valNodeInfo of
        Lit aConstant -> litToTerm aConstant
        App i' args _ -> do
            fTerm <- lookupTerm i'
            resolvedArgs <- traverse (refToTerm i' argDict) args
            pure $ foldl' pApp fTerm resolvedArgs
        Thunk i' -> thunkToTerm i'
        Cata alg val -> cataToTerm alg val
        DataConstructor tn cn fields -> dataConToTerm i argDict tn cn fields
        Match scrut handlers -> matchToTerm scrut handlers
    AnError -> pure pError

matchToTerm :: Ref -> Vector Ref -> CodeGenM PlutusTerm
matchToTerm = undefined

dataConToTerm ::
    Id -> -- the ID of *this* node
    Map Id (Either (Vector Name) (Vector Id)) ->
    TyName ->
    ConstructorName ->
    Vector Ref ->
    CodeGenM PlutusTerm
dataConToTerm i argDict tn cn@(ConstructorName rawCName) args = do
    dtInfo <- lookupDatatype tn
    case view #originalDecl dtInfo of
        -- We assume the opaque encoding has been checked
        OpaqueData{} -> case rawCName of
            "PlutusI" -> iData <$> refToTerm i argDict (args Vector.! 0)
            "PlutusB" -> bData <$> refToTerm i argDict (args Vector.! 0)
            "PlutusConstr" -> do
                termified <- traverse (refToTerm i argDict) args
                let cIx = termified Vector.! 0
                    cArgs = termified Vector.! 1
                pure $ constrData cIx cArgs
            "PlutusList" -> listData <$> traverse (refToTerm i argDict) args
            "PlutusMap" -> mapData <$> traverse (refToTerm i argDict) args
            other -> throwError $ InvalidOpaqueEncoding other
        DataDeclaration _ _ ctors encoding -> case encoding of
            SOP -> do
                ctorIx <- getConstructorIndex tn cn ctors
                resolvedArgs <- traverse (refToTerm i argDict) args
                pure $ pConstr ctorIx resolvedArgs
            PlutusData strategy ->
                -- We are going to assume that the strategy has been checked
                case strategy of
                    EnumData -> plutus_I <$> getConstructorIndex tn cn ctors
                    ProductListData -> pDataList <$> traverse (refToTerm i argDict) args
                    T.ConstrData -> do
                        cIx <- getConstructorIndex tn cn ctors
                        plutus_ConstrData cIx <$> traverse (refToTerm i argDict) args
                    NewtypeData -> refToTerm i argDict (Vector.head args)
            BuiltinStrategy{} -> error "TODO Implement datacon term generator for builtins"

getConstructorIndex ::
    forall (n :: Type).
    (Num n) =>
    TyName ->
    ConstructorName ->
    Vector (Constructor AbstractTy) ->
    CodeGenM n
getConstructorIndex tn cn ctors = case Vector.findIndex (\x -> view #constructorName x == cn) ctors of
    Nothing -> throwError $ ConstructorNotInDatatype tn cn
    Just cIx -> pure $ fromIntegral cIx

cataToTerm :: Ref -> Ref -> CodeGenM PlutusTerm
cataToTerm = undefined

thunkToTerm :: Id -> CodeGenM PlutusTerm
thunkToTerm = undefined

litToTerm :: AConstant -> CodeGenM PlutusTerm
litToTerm = undefined

lamToTerm :: CompT AbstractTy -> Ref -> CodeGenM PlutusTerm
lamToTerm = undefined

forceToTerm :: Ref -> CodeGenM PlutusTerm
forceToTerm = undefined

idToVar :: Id -> PlutusTerm
idToVar = pVar . idToName

refToTerm ::
    Id -> -- This is the Id of the *immediate parent node*. We need that for this to work bottom up
    Map Id (Either (Vector Name) (Vector Id)) -> -- The resolution dictory for args (tells us which names correspond to them)
    Ref ->
    CodeGenM PlutusTerm
refToTerm parentId argDict = \case
    AnId i -> pure $ idToVar i
    AnArg (UnArg db ix) -> do
        let dbInt = review asInt db
            ixInt = review intIndex ix
        case M.lookup parentId argDict of
            Nothing -> throwError $ ArgResolutionFail (ParentIdLookupFailed parentId)
            Just cxt -> case cxt of
                Left _names -> throwError $ ArgResolutionFail (ParentIdPointsAtNames parentId)
                Right idCxt -> case idCxt Vector.!? dbInt of
                    Nothing -> throwError $ ArgResolutionFail (DBIndexOutOfBounds db)
                    Just bindingLamId -> case M.lookup bindingLamId argDict of
                        Nothing -> throwError $ ArgResolutionFail (NoBindingContext bindingLamId)
                        Just hopefullyNames -> case hopefullyNames of
                            Left namesForReal -> pure . pVar $ namesForReal Vector.! ixInt
                            Right _ -> throwError $ ArgResolutionFail (LamIdPointsAtContext bindingLamId)

countOccurs :: Id -> [ASGNode] -> Int
countOccurs i = foldl' go 0
  where
    countId :: Id -> Int
    countId i' = if i == i' then 1 else 0

    countRef :: Ref -> Int
    countRef = \case
        AnId i' -> if i == i' then 1 else 0
        AnArg _ -> 0

    go :: Int -> ASGNode -> Int
    go n = \case
        ACompNode _compTy compNodeInfo -> case compNodeInfo of
            Force r -> n + countRef r
            Lam r -> n + countRef r
            _other -> n
        AValNode _valT valNodeInfo -> case valNodeInfo of
            Lit _aConstant -> n
            App fn args _ -> n + countId fn + sum (countRef <$> args)
            Thunk i' -> n + countId i'
            Cata alg val -> n + countRef alg + countRef val
            DataConstructor _tn _cn fields -> n + sum (countRef <$> fields)
            Match scrut handlers -> n + countRef scrut + sum (countRef <$> handlers)
        AnError{} -> n
