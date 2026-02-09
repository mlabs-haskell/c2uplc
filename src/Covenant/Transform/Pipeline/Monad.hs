module Covenant.Transform.Pipeline.Monad
  ( PassM,
    CodeGen,
    runCodeGen,
    ASTRef (..),
    Datatypes (..),
    RepPolyHandlers (..),
    runPass,
    runPassNoErrors,
    selectHandlerId,
    noteNilFixer,
    initRepPolyHandlers,
  )
where

import Control.Monad.Except (ExceptT (ExceptT), MonadError, runExceptT)
import Control.Monad.RWS.Strict (MonadReader, RWST, runRWST)
import Control.Monad.State.Strict
  ( MonadState (get),
    State,
    evalState,
    modify',
  )
import Covenant.CodeGen.Stubs
  ( HandlerType (Embed, Proj),
    HasStubError,
    MonadStub,
    StubError,
    StubM,
    compileStubM,
    defStubs,
    stubId,
    trySelectHandler,
  )
import Covenant.Data (DatatypeInfo)
import Covenant.ExtendedASG
  ( ExtendedASG,
    MonadASG,
    embeddingId,
    forgetExtendedId,
    projectionId,
  )
import Covenant.Test (Id)
import Covenant.Type (AbstractTy, TyName, ValT)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Void (Void, absurd)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term)

{- I need some kind of unifying abstraction for all the transformation passes here.

   As of right now, everything basically runs in either:
     - An arbitrary `MonadASG m => m ...` monad
     - A `RWS r ExtendedASG` monad.

   All of this needs to be wrapped so that it runs in StubM :: (* -> *) -> * -> *

   We can get a MonadASG instance (and enable StubM operations that depend upon the
   constraint for the inner monad) with something like:

   StubM (StateT ExtendedASG m)

   ... but I think we'd need impossible monad morphisms.

   Maybe if we invert the stack?

   Remember: runRWST :: RWST r w s m a -> r -> s -> m (a, s, w)

   So if we use StubM (State ExtendedASG) as the INNER monad we can do

   type PipelineM r s a = RWST r () s (StubM (State ExtendedASG)) a

   Which I think is what we want? The pipeline runs in StubM (State ExtendedASG) and we can
   tack on or remove additional bits of extra context the individual transformations require.

   I THINK?

   Not sure if we need a MonadStub typeclass? We do not generally want to be forced into writing
   every function with the concrete monad, but we have to do that if the main operations of
   StubM are particular to that concrete monad. I think we do need the class and then this will work.

   Will require rewriting type signatures but not that much else, and things that only need the MonadASG constraint
   can stay as they are.

   This seems like the most sensible solution given the time constraints. A free monad or effects library
   is probably the right choice, but I haven't touched those in years, so this will have to do.
-}

newtype CodeGen a = CodeGen (StubM (State ExtendedASG) a)
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadASG,
      MonadStub,
      HasStubError
    )
    via (StubM (State ExtendedASG))

runCodeGen ::
  ExtendedASG ->
  CodeGen (Term Name DefaultUni DefaultFun ()) ->
  Either StubError (Term Name DefaultUni DefaultFun ())
runCodeGen e (CodeGen act) = evalState (compileStubM defStubs act) e

newtype PassM e r s a = PassM (ExceptT e (RWST r () s CodeGen) a)
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadASG,
      MonadStub,
      MonadReader r,
      MonadState s,
      HasStubError,
      MonadError e
    )
    via (ExceptT e (RWST r () s CodeGen))

runPass ::
  forall (e :: Type) (r :: Type) (s :: Type) (a :: Type).
  r ->
  s ->
  PassM e r s a ->
  CodeGen (Either e (a, s))
runPass r s (PassM act) = do
  runRWST (runExceptT act) r s >>= \case
    (res, st, _) -> case res of
      Left e -> pure $ Left e
      Right x -> pure $ Right (x, st)

runPassNoErrors ::
  forall (r :: Type) (s :: Type) (a :: Type).
  r ->
  s ->
  PassM Void r s a ->
  CodeGen (a, s)
runPassNoErrors r s act =
  runPass r s act >>= \case
    Left err -> absurd err
    Right res -> pure res

-- This is a form of absolute reference for use in the final two passes.
-- ATM it is only used for generated the correct Nil but it could be useful for other
-- things later.
--
-- This is, properly, a reference into a Tree that we have yet to construct from our graph,
-- the name is intentional.
data ASTRef = ASTRef {underLams :: Vector Id, underApps :: Vector Id, appNodeId :: Id}
  deriving stock (Show, Eq, Ord)

data RepPolyHandlers
  = RepPolyHandlers
  { ixedById :: Map Id (Term Name DefaultUni DefaultFun (), HandlerType, ValT AbstractTy),
    ixedByType :: Map (ValT AbstractTy, HandlerType) Id,
    -- This is stupid and shouldn't be here but it is kind of the only sensible place to put it
    -- due to Nil being incredibly weird in how we have to handle it internally -_-
    nilTyFixers :: Set ASTRef
  }
  deriving stock (Show, Eq)

initRepPolyHandlers :: RepPolyHandlers
initRepPolyHandlers = RepPolyHandlers mempty mempty mempty

newtype Datatypes = Datatypes (Map TyName (DatatypeInfo AbstractTy))

{- This is a dumb hack. The pipeline supposes that we, at the very end, make every handler function
   "explicit" in the ASG. I.e. that projections and embeddings have Ids.

   They don't actually *need* to have Ids, but refactoring the pipeline to account for that would
   take more time than I have, so this ensures we can always get an `Id` for every
   proj/embed handler.

   We don't construct synthetic functions here because we should only ever use this at a point where
   those don't actually matter anymore (after analysis).

   This won't work if we use it on non-concrete types. The only reason we don't work w/ `ValT Void`
   is that doing so would require more work (and no time).
-}
selectHandlerId ::
  forall m.
  (MonadStub m, MonadState RepPolyHandlers m) =>
  Datatypes ->
  HandlerType ->
  ValT AbstractTy ->
  m Id
selectHandlerId (Datatypes dtDict) htype valT = do
  (RepPolyHandlers _ byType _) <- get
  case M.lookup (valT, htype) byType of
    Just i -> pure i
    Nothing ->
      trySelectHandler dtDict htype valT >>= \case
        Nothing -> stubId "id"
        Just aHandler -> do
          eid <- case htype of
            Proj -> projectionId
            Embed -> embeddingId
          let i = forgetExtendedId eid
          let updF (RepPolyHandlers byId' byType' nilFixers) =
                RepPolyHandlers
                  (M.insert i (aHandler, htype, valT) byId')
                  (M.insert (valT, htype) i byType')
                  nilFixers
          modify' updF
          pure i

{- This just notes that a given node is a type fixing node for Nil.

   Nil is weird. Every other nullary constructor (no matter how many phantom tyvars it has)
   can be generated very easily. But because UPLC isn't really untyped, we have to be able to
   construct empty list values of the correct type, so we need to keep track of the nodes that
   *fully* determine the type of a given `Nil`.

   The idea is that during rep poly resolution, we will ensure that those nodes (and they will
   always be App nodes) have a fully concretified "function type" so that we can generate the
   correct empty list straightaway.

   This is only for bookkeeping, it doesn't do anything interesting on its own.
-}
noteNilFixer ::
  forall m.
  (MonadStub m, MonadState RepPolyHandlers m) =>
  ASTRef ->
  m ()
noteNilFixer astRef = modify' $ \(RepPolyHandlers a b nilFixers) ->
  RepPolyHandlers a b (S.insert astRef nilFixers)
