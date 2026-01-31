module Covenant.Transform.Pipeline.Monad where

import Control.Monad.RWS.Strict
import Control.Monad.State.Strict

import Control.Monad.Except (MonadError)
import Covenant.CodeGen.Stubs
import Covenant.ExtendedASG
import Data.Kind (Type)

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

instance (Monoid w, MonadStub m) => MonadStub (RWST r w s m) where
    stubData = lift . stubData

    stubExists = lift . stubExists

    -- I don't like this way of implementing this but I am not really sure what else to do.
    -- @Koz any better ideas? :-(
    asTopLevel act = do
        r <- ask
        s <- get
        (res, s', w) <- lift $ runRWST act r s
        tell w
        put s'
        pure res

    _bindStub nm term = lift $ _bindStub nm term

newtype CodeGen a = CodeGen (StubM (State ExtendedASG) a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadASG
        , MonadStub
        , MonadError StubError
        )
        via (StubM (State ExtendedASG))

newtype PassM r s a = PassM (RWST r () s CodeGen a)
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadASG
        , MonadStub
        , MonadReader r
        , MonadState s
        , MonadError StubError
        )
        via (RWST r () s CodeGen)

runPass ::
    forall (r :: Type) (s :: Type) (a :: Type).
    r ->
    s ->
    PassM r s a ->
    CodeGen (a, s)
runPass r s (PassM act) = do
    (a, s', _) <- runRWST act r s
    pure (a, s')
