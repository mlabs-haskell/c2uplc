module Covenant.CodeGen (compile, evalTerm, compilePretty, CodeGenError) where

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

import Covenant.ArgDict ()
import Covenant.CodeGen.Common

import Control.Monad.Except (runExceptT)
import Covenant.ExtendedASG (extendedNodes, unExtendedASG)
import Covenant.JSON (CompilationUnit)
import Covenant.Transform (transformASG)
import Covenant.Transform.Common ( TyFixerFnData (TyFixerFnData))
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

-- evaluation stuff
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (
    ExBudget (ExBudget),
    ExRestrictingBudget (ExRestrictingBudget),
    minusExBudget,
 )
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (ExCPU), ExMemory (ExMemory))
import Prettyprinter
import UntypedPlutusCore (
    Program (Program),
    Term,
    Version (Version),
 )
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

compilePretty = fmap pretty . compile

{- Add optimization pass after UPLC generation

   See: https://github.com/Plutonomicon/plutarch-plutus/blob/treasury-milestone-3/Plutarch/Internal/Term.hs#L829-L853
-}
compile :: CompilationUnit -> Either CodeGenError PlutusTerm
compile cu = runTopDownCompile pipelineData pipelineASG
  where
    trace1 = "asg:\n" <> show (prettyNodes [] nodes) <> "\n\n"
    -- trace2 = "argDict:\n" <> show argResDict <> "\n\n"
    trace3 = "eNodes:\n" <> (show $ extendedNodes pipelineASG) <> "\n\n"
    datatypes = pipelineData R..! #dtDict
    -- (CodeGenM act) = generatePLC pipelineData argResDict nodes
    pipelineData = transformASG cu
    pipelineASG = pipelineData R..! #asg
    -- argResDict = preprocess pipelineASG
    nodes = snd $ unExtendedASG pipelineASG

    prettyNodes acc [] = vcat $ reverse acc
    prettyNodes acc ((UnsafeMkId i, node) : rest) =
        let here = "let" <+> pretty i <+> "=" <+> viaShow node
         in prettyNodes (here : acc) rest

{-
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
                [] -> error "FILL IN THIS CASE"
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
                {- If you put this back it will stop inlining everything
                modify $ M.insert i iVar
                termInner <- go i' node' rest'
                pure $ pLam iName termInner `pApp` thisTerm
                -}
                modify $ M.insert i thisTerm
                go i' node' rest'

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

{- TODO: Intro forms need to have a `Delay` in the generated code b/c they end up as thunks in the
         covenant ASG.
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

lamToTerm ::
    Map Id (Either (Vector Name) (Vector Id)) -> -- our argument resolution dictionary
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
        -- If it weren't for the fact that we do give some things informative variable names, we could just
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
-}
-- TODO: Need to rework this to ignore synthetic (compiler generated) nodes since we really really really
--       want to make sure they definitely get let bound
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

-----------------------------------

-- Returns a pretty error bundle (or at least, like, a string-ey error bundle)
-- or the evaluated term

evalTerm :: PlutusTerm -> Either String PlutusTerm
evalTerm t = case errOrRes of
    Left anErr -> Left $ "Failure!\n  Eval Exception: " <> show anErr <> "\n  Logs: " <> show log
    Right res -> pure res
  where
    (errOrRes, log) = evalTerm' t

-- no budget, don't care yet
evalTerm' ::
    PlutusTerm ->
    ( Either
        (Cek.CekEvaluationException Name PLC.DefaultUni PLC.DefaultFun)
        PlutusTerm
    , [Text]
    )
evalTerm' t =
    case Cek.runCek defaultCekParametersForTesting Cek.counting Cek.logEmitter t of
        (errOrRes, _, logs) -> (errOrRes, logs)
