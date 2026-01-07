module Covenant.CodeGen (compile, compilePretty, CodeGenError) where

import Covenant.ASG (
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
 )
import Covenant.Constant (AConstant (ABoolean, AByteString, AString, AUnit, AnInteger))
import Covenant.Data (DatatypeInfo)
import Covenant.Test (Arg (UnsafeMkArg), Id (UnsafeMkId))
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT,
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
import Control.Monad.Trans.RWS (RWS, evalRWS)

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
    listData,
    mapData,
    pApp,
    pBuiltin,
    pCase,
    pConstr,
    pDelay,
    pError,
    pForce,
    pLam,
    pVar,
    plutus_ConstrData,
 )

import Covenant.ArgDict (preprocess)

import Control.Monad.Except (runExceptT)
import Covenant.ExtendedASG (extendedNodes, unExtendedASG)
import Covenant.JSON (CompilationUnit)
import Covenant.Transform (transformASG)
import Covenant.Transform.Common (PolyRepHandler, TyFixerFnData (TyFixerFnData))
import Covenant.Transform.Pipeline.Common (PipelineData, TransformState)
import Covenant.Transform.TyUtils (idToName)
import Data.Maybe (isJust)
import Data.Row.Records (Rec)
import Data.Row.Records qualified as R
import Debug.Trace
import PlutusCore (Name (Name))
import PlutusCore.MkPlc (mkConstant)
import Prettyprinter
import UntypedPlutusCore (Unique (Unique))

compilePretty = fmap pretty . compile

compile :: CompilationUnit -> Either CodeGenError PlutusTerm
compile cu = trace trace1 $ trace trace2 $ trace trace3 $ fst $ evalRWS (runExceptT act) datatypes M.empty
  where
    trace1 = "asg:\n" <> show nodes <> "\n\n"
    trace2 = "argDict:\n" <> show argResDict <> "\n\n"
    trace3 = "eNodes:\n" <> show (extendedNodes pipelineASG) <> "\n\n"
    datatypes = pipelineData R..! #dtDict
    (CodeGenM act) = generatePLC pipelineData argResDict nodes
    pipelineData = transformASG cu
    pipelineASG = pipelineData R..! #asg
    argResDict = preprocess pipelineASG
    nodes = snd $ unExtendedASG pipelineASG

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

-- N.B. this should always (or almost always) give us a VARIABLE. The state is only a
-- dictionary of terms in case there is some circumstance where we intentionally want to
-- avoid let binding. (I believe in Plutarch it was determined that some constants and/or builtins
-- are cheaper unhoisted for some reason, TODO double check that)
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
    Rec PipelineData ->
    Map Id (Either (Vector Name) (Vector Id)) ->
    [(Id, ASGNode)] ->
    CodeGenM PlutusTerm
generatePLC pipelineData argDict = \case
    [] -> throwError NoASG
    ((i, n) : rest) -> go i n rest
  where
    -- If we want to ensure our synthetic type fixer fn nodes have useful names we need to catch that *here*
    go :: Id -> ASGNode -> [(Id, ASGNode)] -> CodeGenM PlutusTerm
    go i node rest
        | isJust (M.lookup i (pipelineData R..! #tyFixers)) = do
            -- we don't really need to check the tail because the only way this could
            -- be the last node is if we were passed a totally empty ASG (in which case we'd never
            -- do the type fixer transformation anyway and no nodes would exist)
            let TyFixerFnData _ _ _ thisTermCompiled _ nm _ = (pipelineData R..! #tyFixers) M.! i
                UnsafeMkId iInner = i
                fnNm = Name nm (Unique (fromIntegral iInner))
            modify $ M.insert i (pVar fnNm)
            case rest of
                ((i', node') : rest') -> do
                    termInner <- go i' node' rest'
                    pure $ pLam fnNm termInner `pApp` thisTermCompiled
        | isJust (M.lookup i (pipelineData R..! #handlerStubs)) = do
            let stub = (pipelineData R..! #handlerStubs) M.! i
                iName = idToName i
                iVar = pVar iName
            -- though I kind of suspect that inlining everything except an identity fn
            -- will always gives a smaller script and make no perf difference
            modify $ M.insert i iVar
            case rest of
                [] -> pure stub
                ((i', node') : rest') -> do
                    termInner <- go i' node' rest'
                    pure $ pLam iName termInner `pApp` stub
        | otherwise = case rest of
            [] -> nodeToTerm i argDict node
            ((i', node') : rest') -> do
                thisTerm <- nodeToTerm i argDict node
                let iName = idToName i
                let iVar = pVar iName
                modify $ M.insert i iVar
                termInner <- go i' node' rest'
                pure $ pLam iName termInner `pApp` thisTerm

{- For now we're just going to let bind everything. We can fix it later.
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
-}

-- This should ONLY EVER BE CALLED THE FIRST TIME WE ENCOUNTER A NODE IN `generatePLC`
nodeToTerm ::
    Id -> -- The Id of *THIS* node. Needed for arg resolution
    Map Id (Either (Vector Name) (Vector Id)) ->
    ASGNode ->
    CodeGenM PlutusTerm
nodeToTerm i argDict node = case node of
    ACompNode _compTy compNodeInfo -> case compNodeInfo of
        Builtin1 bi1 -> pure $ pBuiltin bi1
        Builtin2 bi2 -> pure $ pBuiltin bi2
        Builtin3 bi3 -> pure $ pBuiltin bi3
        Builtin6 bi6 -> pure $ pBuiltin bi6
        Force r -> forceToTerm i argDict r
        Lam r -> lamToTerm argDict i r
    AValNode _valT valNodeInfo -> case valNodeInfo of
        Lit aConstant -> litToTerm aConstant
        App i' args _ _ -> do
            fTerm <- lookupTerm i'
            resolvedArgs <- traverse (refToTerm i' argDict) args
            pure $ foldl' pApp fTerm resolvedArgs
        Thunk i' -> thunkToTerm i'
        _ -> error "All type fixing pseudo-app nodes should have been removed from the ASG by the point we call this function"
    AnError -> pure pError

thunkToTerm :: Id -> CodeGenM PlutusTerm
thunkToTerm = fmap pDelay . lookupTerm

litToTerm :: AConstant -> CodeGenM PlutusTerm
litToTerm = \case
    AUnit -> pure $ mkConstant () ()
    ABoolean b -> pure $ mkConstant () b
    AnInteger i -> pure $ mkConstant () i
    AByteString bs -> pure $ mkConstant () bs
    AString txt -> pure $ mkConstant () txt

lamToTerm ::
    Map Id (Either (Vector Name) (Vector Id)) -> -- our argument resolution dictionary, tho here we're using it "the other way around"
    Id -> -- the Id of the lambda node
    Ref -> -- body
    CodeGenM PlutusTerm
lamToTerm argDict lamNodeId bodyRef = case M.lookup lamNodeId argDict of
    Just (Left names) -> do
        -- I thiiiink?
        let f = foldl' (\g argN -> g . pLam argN) id names
        resolvedBody <- refToTerm lamNodeId argDict bodyRef
        pure $ f resolvedBody
    _anythingElse ->
        error $
            "Error, expected a Vector of Names in arg res dict entry for lamda id  "
                <> show lamNodeId
                <> " but got "
                <> show _anythingElse

forceToTerm ::
    Id -> -- id of the parent node
    Map Id (Either (Vector Name) (Vector Id)) -> -- arg resolution dict
    Ref -> -- the thing we're forcing
    CodeGenM PlutusTerm
forceToTerm parentId argDict = fmap pForce . refToTerm parentId argDict

refToTerm ::
    Id -> -- This is the Id of the *immediate parent node*. We need that for this to work bottom up
    Map Id (Either (Vector Name) (Vector Id)) -> -- The resolution dictory for args (tells us which names correspond to them)
    Ref ->
    CodeGenM PlutusTerm
refToTerm parentId argDict = \case
    AnId i -> do
        -- Again, this is looking up something which should always or almost always be a variable.
        -- If it weren't for the face that we do give some things informative variable names, we could just
        -- convert the Id directly into its name.
        lookupTerm i
    AnArg (UnsafeMkArg db ix _) -> do
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
            App fn args _ _ -> n + countId fn + sum (countRef <$> args)
            Thunk i' -> n + countId i'
            Cata ty handlers arg -> n + sum (countRef <$> arg `Vector.cons` handlers)
            DataConstructor _tn _cn fields -> n + sum (countRef <$> fields)
            Match scrut handlers -> n + countRef scrut + sum (countRef <$> handlers)
        AnError{} -> n
