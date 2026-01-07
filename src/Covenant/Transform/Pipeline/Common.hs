{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Covenant.Transform.Pipeline.Common where

import Data.Map (Map)

import Data.Set (Set)
import Data.Vector (Vector)

import Control.Monad.RWS.Strict (RWS, put)

import Covenant.ASG (
    ASGNode (ACompNode),
    Id,
    Ref (AnId),
 )
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT,
    CompT,
    TyName,
    ValT,
 )

import Control.Monad.State.Strict (MonadState (get), State, gets, modify', runState)
import Covenant.Data (DatatypeInfo)
import Covenant.Index (Index)
import Covenant.Test (CompNodeInfo (LamInternal))
import Data.Kind (Type)
import Data.Void (Void)

import Covenant.ExtendedASG
import Covenant.MockPlutus (PlutusTerm)
import Covenant.Transform.Common
import Covenant.Transform.TyUtils (AppId, LambdaId (LambdaId))
import Data.Row.Records (HasType, Rec, Row, type (.+), type (.==))
import Data.Row.Records qualified as R
import GHC.TypeLits (KnownSymbol, Symbol)

type PipelineData =
    TransformState
        .+ "handlerStubs" .== Map Id PlutusTerm

type ConcretifyCxt =
    "context" .== Map AppId (Map (Index "tyvar") (ValT Void))
        .+ "callPath" .== Vector LambdaId
        .+ "appPath" .== Vector AppId
        .+ "tyFixers" .== Map Id TyFixerFnData
        .+ "builtinHandlers" .== Map BuiltinFlatT PolyRepHandler
        .+ "identityFn" .== ExtendedId
        .+ "uniqueError" .== ExtendedId

instance (Monoid w) => MonadASG (RWS r w ExtendedASG) where
    getASG = get
    putASG = put

-- Row type synonyms for our various states
type FirstPassMeta =
    "builtinHandlers" .== Map BuiltinFlatT PolyRepHandler
        .+ "identityFn" .== ExtendedId
        .+ "uniqueError" .== ExtendedId

type TransformState =
    FirstPassMeta
        .+ "asg" .== ExtendedASG
        .+ "visited" .== Set ExtendedId
        .+ "dtDict" .== Map TyName (DatatypeInfo AbstractTy)
        .+ "tyFixerData" .== Map TyName TyFixerDataBundle
        .+ "tyFixers" .== Map Id TyFixerFnData

-- Just to help me keep straight all of the various IDs we need to keep track of
-- (i will mess up less if i have to construct this)
newtype UniqueError = UniqueError Id

eLambdaTy :: forall m. (MonadASG m) => LambdaId -> m (CompT AbstractTy)
eLambdaTy (LambdaId l) =
    eNodeAt l >>= \case
        ACompNode compT _ -> pure compT
        _other -> error "Lambda id points at non-comp-node"

mapField ::
    forall (l :: Symbol) (a :: Type) (r :: Row Type).
    (KnownSymbol l, HasType l a r) =>
    R.Label l ->
    (a -> a) ->
    Rec r ->
    Rec r
mapField l f r = R.update l (f (r R..! l)) r

-- I didn't bill for the row stuff, I just got frustrated having to rewrite optics over and over again
-- as I iterated heavily on this module and used this out for convenience while experimenting. I can remove it all later.
unliftMetaM ::
    forall
        (m :: Type -> Type)
        (r :: Row Type)
        (a :: Type).
    (HasType "asg" ExtendedASG r, R.AllUniqueLabels r, MonadASG m, Monad m) =>
    Rec r -> MetaM r a -> m (a, Rec r)
unliftMetaM r act = do
    asg <- getASG
    let rIn = R.update #asg asg r
        (a, rOut) = runMetaM rIn act
    putASG (rOut R..! #asg)
    pure (a, rOut)

-- I dunno what the point of this was
newtype MetaM r a = MetaM (State (Rec r) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadState (Rec r)
        )
        via (State (Rec r))

instance (HasType "asg" ExtendedASG r) => MonadASG (MetaM r) where
    getASG = gets (R..! #asg)
    putASG asg = modify' $ R.update #asg asg

runMetaM :: forall (r :: Row Type) (a :: Type). Rec r -> MetaM r a -> (a, Rec r)
runMetaM aRec (MetaM act) = runState act aRec

syntheticLamNode :: UniqueError -> CompT AbstractTy -> ASGNode
syntheticLamNode (UniqueError errId) funTy = ACompNode funTy (LamInternal (AnId errId))
