{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Covenant.Transform.Pipeline.Common where

import Data.Map (Map)

import Data.Set (Set)
import Data.Vector (Vector)

import Control.Monad.RWS.Strict (MonadReader, RWS, ask, put, runRWS)

import Covenant.ASG (
    ASGNode (ACompNode),
    Id,
    Ref (AnId),
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT,
    CompT,
    TyName (..),
    ValT (Abstraction, BuiltinFlat),
 )

import Control.Monad.State.Strict (MonadState (get), State, gets, modify', runState)
import Covenant.Data (DatatypeInfo)
import Covenant.Index (Index)
import Covenant.Test (CompNodeInfo (LamInternal))
import Data.Kind (Type)
import Data.Void (Void)

import Covenant.ArgDict (pValT, pVec)
import Covenant.ExtendedASG
import Covenant.MockPlutus (PlutusTerm, pVar, ppTerm)
import Covenant.Transform.Common
import Covenant.Transform.TyUtils (AppId, LambdaId (LambdaId), idToName)
import Data.Map qualified as M
import Data.Row.Records (HasType, Rec, Row, type (.+), type (.==))
import Data.Row.Records qualified as R
import Data.Text qualified as T
import Data.Vector qualified as Vector
import Debug.Trace (traceM)
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

{- We need somewhere to stash these Ids (i.e. a reader context) since it's awkward to
   insert them into the ASG before we complete our analysis pass in the AppTranformM monad
-}
data PolyRepHandler = PolyRepHandler {project :: Id, embed :: Id} deriving stock (Show, Eq)

-- N.B. we need the `Map BuiltinFlatT Id` to record the projection/embedding function ids
-- TODO: Errors?
newtype AppTransformM a = AppTransformM (RWS (Map TyName (DatatypeInfo AbstractTy), Map BuiltinFlatT PolyRepHandler) () ExtendedASG a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadReader (Map TyName (DatatypeInfo AbstractTy), Map BuiltinFlatT PolyRepHandler)
        , MonadState ExtendedASG
        )
        via (RWS (Map TyName (DatatypeInfo AbstractTy), Map BuiltinFlatT PolyRepHandler) () ExtendedASG)

instance MonadASG AppTransformM where
    getASG = get
    putASG = put

runAppTransformM ::
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    ExtendedASG ->
    AppTransformM a ->
    (a, ExtendedASG)
runAppTransformM datatypes polyRepHandlers asg (AppTransformM act) = (x, i)
  where
    (x, i, _) = runRWS act (datatypes, polyRepHandlers) asg

-- stupid helpers

-- Something has gone really, horrifically wrong if something is annotated w/ a datatype type
-- and we don't know about the datatype at this point.
lookupDatatypeInfo :: TyName -> AppTransformM (DatatypeInfo AbstractTy)
lookupDatatypeInfo tn@(TyName tnInner) = do
    (dtDict, _) <- ask
    case M.lookup tn dtDict of
        Just res -> pure res
        Nothing -> error $ "No datatype info for " <> T.unpack tnInner

lookupPolyRepHandler :: ValT AbstractTy -> AppTransformM (Maybe PolyRepHandler)
lookupPolyRepHandler = \case
    BuiltinFlat biFlat -> do
        (_, repHandlerMap) <- ask
        pure $ M.lookup biFlat repHandlerMap
    _ -> pure Nothing

{- This is a helper for constructing a function which is used in all of the type fixer
   code generators to locate the correct plutus term corresponding to projection or embedding
   functions for a given type that potentially needs to be projected or embedded.

   In practice, locating this requires both:
     1. Information specific to the datatype. For type variables, we add the handlers as arguments to the
        type fixer "synthetic function".
     2. Generic information for statically known concrete builtin flat types, which we access from the AppTransformM
        monadic context.

   Largely a convenience b/c the implementation has to be somewhat ugly and is effectively duplicated several times.
-}
resolvePolyRepHandler :: -- Gets the projection or embedding we need (if it exists)
    TyFixerNodeKind ->
    -- Gives us the index into the list of terms representing
    -- function arguments which corresponds to the projection/embedding function
    Map (Index "tyvar") Int ->
    -- The thing we use the previous argument to index into; the arguments to the
    -- function-alized type fixer for the datatype.
    Vector PlutusTerm ->
    -- This is the index of the 'r' variable if we're in a catamorphism.
    -- This should ONLY be `Just` if we're working with a cata.
    -- We use this to determine whether to return 'self' (which
    -- is always the 0th element of the previous vector for a cata
    -- and which functions somewhat analogously to a projection/embedding function)
    Maybe (Index "tyvar") ->
    ValT AbstractTy ->
    AppTransformM (Maybe PlutusTerm)
resolvePolyRepHandler nodeKind handlerArgPosDict lamArgVars maybeR valT =
    traceM msg >> case valT of
        Abstraction (BoundAt _ indx) -> case M.lookup indx handlerArgPosDict of
            Nothing -> case maybeR of
                Just rIndex | indx == rIndex -> traceM "resolve r" >> pure . Just $ lamArgVars Vector.! 0
                _ -> traceM "resolve no handler no r" >> pure Nothing
            Just hIx -> traceM ("resolve result: " <> show hIx) >> pure . pure $ lamArgVars Vector.! hIx
        bi@(BuiltinFlat _) -> do
            mRepHandler <- lookupPolyRepHandler bi
            case mRepHandler of
                Nothing -> traceM "resolve no polyRepHandler" >> pure Nothing
                Just polyRepHandler -> do
                    let handler = extractHandler polyRepHandler
                        msg = "resolve found poly rep handler " <> ppTerm handler
                    traceM msg
                    pure . Just $ handler
        _anythingElse -> traceM "resolve nothing catchall" >> pure Nothing
  where
    msg =
        "\nresolvePolyRep:\n  "
            <> show handlerArgPosDict
            <> "\n   valTy: "
            <> pValT valT
            <> "\n  argVars: "
            <> pVec ppTerm lamArgVars
            <> "\n  maybeR: "
            <> show maybeR

    extractHandler :: PolyRepHandler -> PlutusTerm
    extractHandler (PolyRepHandler projF embedF) = case nodeKind of
        MatchNode -> pVar . idToName $ projF
        CataNode -> pVar . idToName $ projF
        IntroNode -> pVar . idToName $ embedF
