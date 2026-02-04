{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Covenant.ExtendedASG (
    ExtendedId (WrappedSrc, IdentityFn, EphemeralError, Projection, Embedding, TyFixerFn),
    ExtendedKey (eSafeNodeAt),
    eNodeAt,
    forgetExtendedId,
    ExtendedASG,
    extendedNodes,
    wrapASG,
    MonadASG (..),
    nextId,
    identityFnId,
    ephemeralErrorId,
    projectionId,
    embeddingId,
    tyFixerFnId,
    eInsert,
    eTopLevelSrcNode,
    resolveExtended,
    unExtendedASG,
    removeEphemeralError,
    -- test util (mainly for debugging generated PLC w/o having to run the whole compiler)
    runWithEmptyASG,
) where

import Control.Monad.Except (ExceptT)
import Control.Monad.RWS.Strict (MonadState (..), MonadTrans (lift), RWST, modify')
import Control.Monad.State.Strict (State, StateT, evalState)
import Covenant.ASG (ASG (ASG), ASGNode, Id, topLevelId)
import Covenant.Test (Id (UnsafeMkId))
import Data.Bifunctor (first)
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)

data ExtendedId
    = -- The original Ids we get after deserializing
      WrappedSrcId Id
    | -- The Id of a single identity function that we need to know exists
      IdentityFnId Id
    | -- The Id of an error node. We need at least one as a placeholder for synthetic
      -- functions which cannot be given a well-typed Covenant body, but which
      -- can be generated in UPLC
      EphemeralErrorId Id
    | -- A projection function, used to resolve representational polymorphism
      ProjectionId Id
    | -- An embedding function, used to resolve representational polymorphism
      EmbeddingId Id
    | -- An Id reprsenting one of:
      --  - A data constructor intro function (Just, Nothing, Left, Right, Cons, Nil, etc)
      --  - A destructor function for a datatype, such as match_Maybe or match_List
      --  - A catamorphism for tearing down recursive datatypes
      TyFixerFnId Id
    deriving stock (Eq, Show)

{- This is largely the reason to have ExtendedId.

   We want to add to our ASG and maintain the ability to look up nodes by their Id, but because we are forced to
   increment Ids from the original maximum ASG Id in order to generate fresh references, we need some way of
   sorting the Ids which requires information external to their underlying machine Word.

   We need this because there is a "natural" traversal order for the main code generation traversal, but if we must
   add to the ASG, we cannot use that traversal order, since our additions (which have no dependencies, or only have
   dependencies we add) come "at the end" in the default Id ordering, whereas we need them to come "at the beginning"
   (with their own kind of order)

   We want the (low to high) order here to be:

     0. Error (we are going to remove this anyway so it doesn't matter)
     1. Projection / Embedding (doesn't matter which comes first)
     2. Identity
     3. All TypeFixer stuff
     4. WrappedId

-}
instance Ord ExtendedId where
    compare eId1 eId2 = case (eId1, eId2) of
        -- Wrapped comes at the end (asc sort)
        (WrappedSrcId i1, WrappedSrcId i2) -> compare i1 i2
        (_, WrappedSrcId _) -> LT
        (WrappedSrcId _, _) -> GT
        -- Then TyFixerStuff, which the ASG depends on
        (TyFixerFnId i1, TyFixerFnId i2) -> compare i1 i2
        (_, TyFixerFnId _) -> LT
        (TyFixerFnId _, _) -> GT
        -- Then our identity function
        (IdentityFnId i1, IdentityFnId i2) -> compare i1 i2
        (_, IdentityFnId _) -> LT
        (IdentityFnId _, _) -> GT
        -- The rest of the cases don't actually matter so long as they come before the above cases
        _ -> compare (forgetExtendedId eId1) (forgetExtendedId eId2)

forgetExtendedId :: ExtendedId -> Id
forgetExtendedId = \case
    WrappedSrcId i -> i
    IdentityFnId i -> i
    EphemeralErrorId i -> i
    ProjectionId i -> i
    EmbeddingId i -> i
    TyFixerFnId i -> i

-- The final argument is the maximum Id
data ExtendedASG = ExtendedASG (Map ExtendedId ASGNode) (Map Id ExtendedId) Id

extendedNodes :: ExtendedASG -> Map ExtendedId ASGNode
extendedNodes (ExtendedASG nodes _ _) = nodes

unExtendedASG :: ExtendedASG -> (Id, [(Id, ASGNode)])
unExtendedASG (ExtendedASG nodes _ _) = (topSrcId, rawASG)
  where
    topSrcId = forgetExtendedId . fst $ M.findMax nodes
    rawASG = first forgetExtendedId <$> M.toList nodes

wrapASG :: Map Id ASGNode -> ExtendedASG
wrapASG asg = ExtendedASG nodes idResolver (fst . M.findMax $ asg)
  where
    nodes :: Map ExtendedId ASGNode
    nodes = M.mapKeys WrappedSrcId asg

    idResolver :: Map Id ExtendedId
    idResolver = M.fromList . map (\x -> (x, WrappedSrcId x)) . M.keys $ asg

-- sry koz ill delete it later
class ExtendedKey a where
    eSafeNodeAt :: a -> ExtendedASG -> Maybe ASGNode

instance ExtendedKey ExtendedId where
    eSafeNodeAt eid (ExtendedASG m _ _) = M.lookup eid m

instance ExtendedKey Id where
    eSafeNodeAt i (ExtendedASG m n _) = M.lookup i n >>= flip M.lookup m

-- | Unsafe
eNodeAt ::
    forall (a :: Type) (m :: Type -> Type).
    (MonadASG m, ExtendedKey a, Show a) => a -> m ASGNode
eNodeAt k =
    getASG >>= \asg -> case eSafeNodeAt k asg of
        Nothing -> error $ "eNodeAt: Error: Key " <> show k <> " not found in ExtendedASG"
        Just res -> pure res

resolveExtended ::
    forall (m :: Type -> Type).
    (MonadASG m) =>
    Id ->
    m ExtendedId
resolveExtended i = do
    ExtendedASG _ m _ <- getASG
    pure $ m M.! i

-- There's probably a better way to do this w/ optics, but
-- i need some way abstract over the capability to
-- get and set the ASG part of what may be a complex state
class (Monad m) => MonadASG m where
    getASG :: m ExtendedASG
    putASG :: ExtendedASG -> m ()

instance MonadASG (State ExtendedASG) where
    getASG = get
    putASG = put

instance (Monoid w, MonadASG m) => MonadASG (RWST r w s m) where
    getASG = lift getASG
    putASG = lift . putASG

instance (MonadASG m) => MonadASG (ExceptT e m) where
    getASG = lift getASG
    putASG = lift . putASG

-- test util
runWithEmptyASG :: forall r. (forall m. (MonadASG m) => m r) -> r
runWithEmptyASG f = evalState f (ExtendedASG M.empty M.empty (UnsafeMkId 0))

nextId :: forall (m :: Type -> Type). (MonadASG m) => m Id
nextId = do
    (ExtendedASG nodes resolver (UnsafeMkId s)) <- getASG
    let newId = UnsafeMkId (s + 1)
    putASG $ ExtendedASG nodes resolver newId
    pure newId

-- Helpers to ensure we can only construct keys within the monad, so we *can't* screw up the maximum Id
-- or create a conflict (there isn't one of these for 'Wrapped')
identityFnId :: (MonadASG m) => m ExtendedId
identityFnId = IdentityFnId <$> nextId

ephemeralErrorId :: (MonadASG m) => m ExtendedId
ephemeralErrorId = EphemeralErrorId <$> nextId

projectionId :: (MonadASG m) => m ExtendedId
projectionId = ProjectionId <$> nextId

embeddingId :: (MonadASG m) => m ExtendedId
embeddingId = EmbeddingId <$> nextId

tyFixerFnId :: (MonadASG m) => m ExtendedId
tyFixerFnId = TyFixerFnId <$> nextId

-- Pattern Synonyms for matching
pattern WrappedSrc :: Id -> ExtendedId
pattern WrappedSrc i <- WrappedSrcId i

pattern IdentityFn :: Id -> ExtendedId
pattern IdentityFn i <- IdentityFnId i

pattern EphemeralError :: Id -> ExtendedId
pattern EphemeralError i = EphemeralErrorId i

pattern Projection :: Id -> ExtendedId
pattern Projection i = ProjectionId i

pattern Embedding :: Id -> ExtendedId
pattern Embedding i = EmbeddingId i

pattern TyFixerFn :: Id -> ExtendedId
pattern TyFixerFn i = TyFixerFnId i

{-# COMPLETE WrappedSrc, IdentityFn, EphemeralError, Projection, Embedding, TyFixerFn #-}

-- If I wrote that ord instance right, this give us the entry point into the ORIGINAL asg.
-- It should always return a WrappedSrcId
eTopLevelSrcNode :: forall m. (MonadASG m) => m (ExtendedId, ASGNode)
eTopLevelSrcNode = do
    ExtendedASG m _ _ <- getASG
    pure . M.findMax $ m

-- Besides creating two ASGs and intentionally mixing up the keys, this should all guarantee that
-- collisions are totally impossible and that every node has a correct, informative ExtendedId
eInsert :: forall m. (MonadASG m) => ExtendedId -> ASGNode -> m ()
eInsert eid node = do
    (ExtendedASG nodes resolver maxId) <- getASG
    let nodes' = M.insert eid node nodes
        resolver' = M.insert (forgetExtendedId eid) eid resolver
    putASG $ ExtendedASG nodes' resolver' maxId

removeEphemeralError :: ExtendedId -> ExtendedASG -> ExtendedASG
removeEphemeralError eid (ExtendedASG nodes resolver maxId) = case eid of
    EphemeralError i ->
        let nodes' = M.delete eid nodes
         in ExtendedASG nodes' resolver maxId
    _somethingElse -> error $ "removeEphemeralError called with: " <> show _somethingElse <> ", which is not an ephemeral error ID"
