{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, asks, execRWS, local, modify, put, runRWS)

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
import Control.Monad (join, when, unless)
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
import Covenant.Transform.TyUtils (countToAbstractions,
                                   getInstantiations, resolveVar, substCompT, LambdaId (LambdaId), AppId (AppId), compTArgSchema, instantiationHelper, decideConcrete, substitute)
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
import GHC.TypeLits (Symbol)
import GHC.TypeLits (KnownSymbol)

import Covenant.Transform.Pipeline.Common
import Covenant.Transform.Pipeline.ElimTyFixers
import Covenant.Transform.Pipeline.FirstPass
import Covenant.Transform.Pipeline.MkTyFixerFnData
import Covenant.Transform.Pipeline.ResolveRepPoly 

transformASG :: CompilationUnit -> Rec TransformState
transformASG (CompilationUnit datatypes asg _) = flip evalState extended $ do
    let dtDict = unsafeMkDatatypeInfos (Vector.toList datatypes)
    firstPassMeta <- firstPass
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
                .+ #tyFixers .== M.empty

    asgBundle1 <-  snd <$> unliftMetaM transformState transformTypeFixerNodes
    let initConcretifyCxt :: Rec ConcretifyCxt
        initConcretifyCxt = #context .== M.empty
                        .+ #callPath .== Vector.empty
                        .+ #appPath .== Vector.empty
                        .+ #tyFixers .== (asgBundle1 R..! #tyFixers)
                        .+ #builtinHandlers .== (firstPassMeta R..! #builtinHandlers)
                        .+ #identityFn .== (firstPassMeta R..! #identityFn)
                        .+ #uniqueError .== (firstPassMeta R..! #uniqueError)
    transformedASG <- getASG
    let (_,finalASG,_) = runRWS resolveRepPoly initConcretifyCxt transformedASG
    let asgBundleFinal = R.update #asg finalASG asgBundle1
    pure asgBundleFinal
  where
    extended :: ExtendedASG
    extended = wrapASG asg
