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
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId, ASGNodeType (ValNodeType), BoundTyVar, typeASGNode,
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar, PlutusDataConstructor (..),
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (MonadReader, Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), State, StateT, evalState, modify', runState, execState, gets)
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
import Covenant.Test (Id (UnsafeMkId), Arg (UnsafeMkArg), CompNodeInfo (ForceInternal), ValNodeInfo (AppInternal))
import Data.Foldable (
    find,
    foldl',
    traverse_,
 )
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, preview, review, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

import Covenant.JSON

import Control.Monad (foldM)
import Covenant.Transform.Cata
import Covenant.Transform.Common
import Covenant.Transform.Elim
import Covenant.Transform.Intro
import qualified Data.Set as Set
import Covenant.Concretify (getInstantiations, substCompT, countToAbstractions, resolveVar)

data UnsafeASG = UnsafeASG
    { asgNodes :: Map Id ASGNode
    , currentTopLevelId :: Id
    , maxId :: Id
    , builtinHandlers :: Map BuiltinFlatT PolyRepHandler
    , tyFixerDict :: Map TyName TyFixerDataBundle
    , datatypes :: Map TyName (DatatypeInfo AbstractTy)
    -- This is the Id of an error node that we use as the body of the "synthetic" functions
    -- we construct for the functionalized type fixers. The *actual* PLC body is generated when we
    -- construct type fixer data. We need to keep track of this so that we can ignore or remove it later.
    , ephemeralError :: EphemeralError
    }

intT :: ValT AbstractTy
intT = BuiltinFlat IntegerT

byteStringT :: ValT AbstractTy
byteStringT = BuiltinFlat ByteStringT

-- From here on out the top level node CANNOT BE ASSUMED TO BE THE HIGHEST NODE NUMERICALLY.
-- This is annoying but there really isn't a sensible way around it.
--
-- We also have to remember to "catch" the IDs for these functions during codegen
-- since they won't have a body, so we're going to have to keep the map around for a while too.
--
-- REVIEW: Don't we need to keep track of the original top level ID too? ugh
mkProjectionsAndEmbeddings :: ASG -> (Map BuiltinFlatT PolyRepHandler, Id, Map Id ASGNode)
mkProjectionsAndEmbeddings asg@(ASG m) = (builtins, newMaxId, newASG)
  where
    incId :: State Id Id
    incId = do
        old <- get
        let new = unsafeNextId old
        modify' $ const new
        pure new

    newASG =
        foldl'
            ( \acc (PolyRepHandler proj emb) ->
                M.insert proj AnError . M.insert emb AnError $ acc
            )
            m
            builtins
    (builtins, newMaxId) = flip runState topId $ do
        projIntId <- incId
        embedIntId <- incId
        let intHandler = PolyRepHandler{project = projIntId, embed = embedIntId}
        projBSId <- incId
        embedBSId <- incId
        let bsHandler = PolyRepHandler{project = projBSId, embed = embedBSId}
        pure $ M.fromList [(IntegerT, intHandler), (ByteStringT, bsHandler)]
    topId = topLevelId asg

unsafeNextId :: Id -> Id
unsafeNextId (UnsafeMkId i) = UnsafeMkId (i + 1)

mkTypeFixerFnData ::
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    Id ->
    -- The id returned is the new maximum id
    (Map TyName TyFixerDataBundle, Id)
mkTypeFixerFnData datatypes biRepHandlers maxId =
    runAppTransformM datatypes biRepHandlers maxId $ do
        let allTyNames = M.keys datatypes
        foldM go M.empty allTyNames
  where
    go :: Map TyName TyFixerDataBundle -> TyName -> AppTransformM (Map TyName TyFixerDataBundle)
    go acc tn = do
        destructorData <- mkDestructorFunction tn
        constructorData@(IntroData v) <- mkConstructorFunctions tn
        -- If we have no constructor functions nor match functions, our datatype is 'void' and we can ignore it
        if null destructorData && null v
          then pure acc
          else do
            cataData <- mkCatamorphism tn
            let thisBundle = TyFixerDataBundle constructorData destructorData cataData
            pure $ M.insert tn thisBundle acc 

    mkTypeFixerLookupTable :: Map Id TyFixerFnData -> Map TyName Id
    mkTypeFixerLookupTable = M.foldlWithKey' (\acc i tffData -> M.insert (mfTyName tffData) i acc) M.empty

-- Just to help me keep straight all of the various IDs we need to keep track of
newtype EphemeralError = EphemeralError Id

{- Rewrites type fixer nodes into applications.

   This also constructs and inserts dummy functions into the ASG
-}
transformTypeFixerNodes :: UnsafeASG -> UnsafeASG
transformTypeFixerNodes asg@(UnsafeASG nodes currTop maxId builtinHandlers tyFixers dtDict magicErr)
  =  undefined
 where
   EphemeralError errId = magicErr
   -- we're going to collect all of the modified nodes all at once and then replace them
   -- at the end. This is largely for easier debugging, since it will make it easier to observe all of the
   -- changes in one place if I have to trace them (vs trying to sort through a trace of ALL of the nodes)
   -- NOTE: This will also contain all of the synthetic function dummy nodes we need.
   modifiedNodes :: Map Id ASGNode
   modifiedNodes = execState (go currTop) M.empty

   resolveCtorIx :: TyName -> ConstructorName -> Maybe Int
   resolveCtorIx tn cn = do
     dtInfo <- M.lookup tn dtDict
     case view #originalDecl dtInfo of
       OpaqueData _ ctors  -> do
         -- TODO/REVIEW: NEED TO CHECK THAT THIS NAMING IS CONSISTENT WITH ANYWHERE ELSE WE HANDLE THIS
         let (ConstructorName inner) = cn
         plutusDataCtor <- case inner of
                                "I" -> Just PlutusI
                                "B" -> Just PlutusB
                                "Constr" -> Just PlutusConstr
                                "List" -> Just PlutusList
                                "Map" -> Just PlutusMap
                                _ -> Nothing
         Vector.findIndex (== plutusDataCtor) (Vector.fromList . Set.toList $ ctors)
       DataDeclaration _ _ ctors _ -> Vector.findIndex (\(Constructor cNm' _) -> cNm' == cn) ctors

     
   -- Not working with a "safe" ASG so we need something like this to avoid an absurd amount of
   -- "maybe"-ing. We'll only ever use it on Ids in the original ASG (that's the other reason
   -- I don't modify the ASG during this procedure) so it's safe
   unsafeNodeAt :: Id -> ASGNode
   unsafeNodeAt i = nodes M.! i

   unsafeDatatypeName :: ValT AbstractTy -> TyName
   unsafeDatatypeName = \case
     Datatype tn _ -> tn
     other -> error $ "unsafeDatatypeName called on non-datatype ValT: " <> show other

   -- only use this on things that have to be a value type (i.e. scrutinees)
   unsafeRefType :: Ref -> ValT AbstractTy
   unsafeRefType = \case
     AnArg (UnsafeMkArg _ _ ty) -> ty
     AnId i -> case typeASGNode (unsafeNodeAt i) of
       ValNodeType ty -> ty
       other -> error $ "UnsafeRefType called on an Id with a non-ValT type: " <> show other

   alreadyVisited :: Id -> State (Map Id ASGNode) Bool
   alreadyVisited i = isJust <$> gets (M.lookup i)

   go :: Id -> State (Map Id ASGNode) ()
   go i = alreadyVisited i >>= \case
     True -> pure ()
     False -> case unsafeNodeAt i of
       AnError -> pure ()
       ACompNode compT compNode -> case compNode of
         Lam ref -> goRef ref
         Force ref -> goRef ref
         _ -> pure ()
       AValNode valT valNode -> case valNode of
          Thunk child -> go child
          App fn args _ _ -> do
            go fn
            traverse_ goRef args
          Cata cataT handlers arg -> do
            traverse_ goRef handlers
            goRef arg
            let tn = unsafeDatatypeName (unsafeRefType arg)
            case cataData =<< M.lookup tn tyFixers of
              Nothing -> error
                          $ "Fatal Error: No type fixer function data for catamorphisms on " <> show tn
              Just (CataData cataId cataFnData) -> do
                let TyFixerFnData _nm _enc cataFnPolyTy _compiled _schema _fnName _ = cataFnData
                    scrutTy = unsafeRefType arg
                    handlerTypes = unsafeRefType <$>  Vector.toList handlers
                    cataFnConcrete =applyArgs cataFnPolyTy (scrutTy:handlerTypes)
                    newValNode = AppInternal cataId (Vector.cons arg handlers) Vector.empty cataFnConcrete
                    newASGNode = AValNode valT newValNode
                modify' $ M.insert i newASGNode
                -- NOTE: This is just a placeholder tagged with the polymorphic function type, which we need.
                --       The body is a reference to a single error node that we track and will ignore/remove.
                --       TODO: There's only one of these for each type so add a check to save us work if we already did it
                let syntheticCataFnNode = ACompNode cataFnPolyTy (ForceInternal (AnId errId))
                modify' $ M.insert cataId syntheticCataFnNode
          Match scrut handlers -> do
            -- NOTE/FIXME/REVIEW/BUG: PROBABLY NEED TO DE-THUNK HANDLER TYPES HERE
            traverse_ goRef handlers
            goRef scrut
            let scrutTy = unsafeRefType scrut
                handlerTypes = unsafeRefType <$> Vector.toList handlers
                tn = unsafeDatatypeName scrutTy
            case matchData =<< M.lookup tn tyFixers of
              Nothing -> error
                          $ "Fatal Error: No type fixer function data for pattern matches on " <> show tn
              Just (MatchData matchId matchFnData) -> do
                let TyFixerFnData _nm _enc matchFnPolyTy _compiled _schema _fnName _ = matchFnData
                    matchFnConcrete = applyArgs matchFnPolyTy (scrutTy:handlerTypes)
                    newValNode = AppInternal matchId (Vector.cons scrut handlers) Vector.empty matchFnConcrete
                    newASGNode = AValNode valT newValNode
                modify' $ M.insert i newASGNode
                -- NOTE: See previous note
                let syntheticMatchFnNode = ACompNode matchFnPolyTy (ForceInternal (AnId errId))
                modify' $ M.insert matchId syntheticMatchFnNode
          DataConstructor tn ctorName ctorArgs -> do
            traverse_ goRef ctorArgs
            let argTys = unsafeRefType <$> Vector.toList ctorArgs
            case introData <$> M.lookup tn tyFixers of
              Nothing -> error
                           $ "Fatal Error: No type fixer function data for datatype introductions for type " <> show tn
              Just (IntroData constrFunctions) -> case resolveCtorIx tn ctorName of
                Nothing -> error $ "Fatal Error: No data for constructor " <> show ctorName <> " found in type " <> show tn
                Just ctorIx -> do
                  let (ctorFnId,ctorFnData) = constrFunctions Vector.! ctorIx
                      TyFixerFnData _nm _enc ctorFnPolyTy _compiled _schema _fnName _ = ctorFnData
                      ctorFnConcrete = applyArgs ctorFnPolyTy argTys
                      newValNode = AppInternal ctorFnId ctorArgs Vector.empty ctorFnConcrete
                      newASGNode = AValNode valT newValNode
                  modify' $ M.insert i newASGNode
                  -- NOTE: See previous note
                  let syntheticCtorFnNode = ACompNode ctorFnPolyTy (ForceInternal (AnId errId))
                  modify' $ M.insert ctorFnId syntheticCtorFnNode
    where
      goRef = \case
        AnId child -> go child
        AnArg{} -> pure () 

applyArgs :: CompT AbstractTy -> [ValT AbstractTy] -> CompT AbstractTy
applyArgs compT [] = compT
-- I *think* we ignore the result when determining the substitutions and then substitute into it to reconstruct
-- the type.
applyArgs polyFun@(CompN cnt (ArgsAndResult fnSigArgs _)) args = cleanup concreteFn
  where
    vars :: [AbstractTy]
    vars = Vector.toList $ countToAbstractions cnt

    instantiations :: Map AbstractTy (ValT AbstractTy)
    instantiations = flip runReader 0 $
                         getInstantiations vars (Vector.toList fnSigArgs) args

    concreteFn :: CompT AbstractTy
    concreteFn = substCompT id instantiations polyFun

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
    substitutions = Vector.ifoldl'
                      (\acc newIx oldTV ->
                         let tvIx = fromJust $ preview intIndex newIx
                             newTv = Abstraction (BoundAt Z tvIx)
                         in M.insert oldTV newTv acc
                      ) M.empty remainingLocalVars


    remainingLocalVars :: Vector AbstractTy
    remainingLocalVars =   Vector.fromList 
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
      ThunkT (CompN _ (ArgsAndResult thunkArgs thunkRes)) -> local (+1) $ do
          let toTraverse = Vector.toList $ Vector.snoc thunkArgs thunkRes
          Set.unions <$> traverse collectLocalVars toTraverse
      Datatype _ dtArgs -> Set.unions <$> traverse collectLocalVars (Vector.toList dtArgs)




retTy :: CompT a -> ValT a
retTy (CompN _ (ArgsAndResult _ res)) = res
