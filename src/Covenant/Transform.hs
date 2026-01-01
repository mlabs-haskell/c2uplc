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
    topLevelId,
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
    tyvar,
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (MonadReader, Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), State, StateT, evalState, modify', runState)
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

import Covenant.JSON

import Control.Monad (foldM)
import Covenant.Transform.Cata
import Covenant.Transform.Common
import Covenant.Transform.Elim
import Covenant.Transform.Intro

data UnsafeASG = UnsafeASG
    { asgNodes :: Map Id ASGNode
    , currentTopLevelId :: Id
    , maxId :: Id
    , builtinHandlers :: Map BuiltinFlatT PolyRepHandler
    , tyFixerDict :: TyFixerDict
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

    unsafeNextId (UnsafeMkId i) = UnsafeMkId (i + 1)
    topId = topLevelId asg

newtype TyFixerDict = TyFixerDict (Map Id TyFixerFnData, Map TyName Id)

lookupFixerByName :: TyName -> TyFixerDict -> Maybe TyFixerFnData
lookupFixerByName tn (TyFixerDict (idDict, nameDict)) = M.lookup tn nameDict >>= flip M.lookup idDict

lookupFixerById :: Id -> TyFixerDict -> Maybe TyFixerFnData
lookupFixerById i (TyFixerDict (idDict, _)) = M.lookup i idDict

mkTypeFixerFnData ::
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    Id ->
    (TyFixerDict, Id)
mkTypeFixerFnData datatypes biRepHandlers maxId =
    runAppTransformM datatypes biRepHandlers maxId $ do
        let allTyNames = M.keys datatypes
        idDict <- foldM go M.empty allTyNames
        let nameDict = mkTypeFixerLookupTable idDict
        pure $ TyFixerDict (idDict, nameDict)
  where
    go :: Map Id TyFixerFnData -> TyName -> AppTransformM (Map Id TyFixerFnData)
    go acc tn = do
        destructorData <- mkDestructorFunction tn
        constructorData <- mkConstructorFunctions tn
        cataData <- mkCatamorphism tn
        pure $ M.unions [destructorData, constructorData, cataData, acc]

    mkTypeFixerLookupTable :: Map Id TyFixerFnData -> Map TyName Id
    mkTypeFixerLookupTable = M.foldlWithKey' (\acc i tffData -> M.insert (mfTyName tffData) i acc) M.empty

{- Rewrites type fixer nodes into applications.

   This also constructs and inserts dummy functions into the ASG
-}
transformTypeFixerNodes :: UnsafeASG -> UnsafeASG
transformTypeFixerNodes _ = undefined
