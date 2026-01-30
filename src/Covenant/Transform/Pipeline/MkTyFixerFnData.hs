{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.MkTyFixerFnData where

import Data.Map (Map)
import Data.Map qualified as M
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT, TyName,
 )

import Covenant.Data (DatatypeInfo)


import Control.Monad (foldM)
import Covenant.ExtendedASG
import Covenant.Transform.Cata
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Covenant.Transform.Elim
import Covenant.Transform.Intro

mkTypeFixerFnData ::
    forall m.
    (MonadASG m) =>
    Map TyName (DatatypeInfo AbstractTy) ->
    Map BuiltinFlatT PolyRepHandler ->
    m (Map TyName TyFixerDataBundle)
mkTypeFixerFnData datatypes biRepHandlers =
    liftAppTransformM $ do
        let allTyNames = M.keys datatypes 
        foldM go M.empty allTyNames
  where
    liftAppTransformM :: AppTransformM a -> m a
    liftAppTransformM act = do
        asg <- getASG
        let (res, newASG) = runAppTransformM datatypes biRepHandlers asg act
        putASG newASG
        pure res

    go :: Map TyName TyFixerDataBundle -> TyName -> AppTransformM (Map TyName TyFixerDataBundle)
    go acc tn = do
        destructorData <- mkDestructorFunction tn
        constructorData <- mkConstructorFunctions tn
        -- If we have no constructor functions nor match functions, our datatype is 'void' and we can ignore it
        if null destructorData && null constructorData
            then pure acc
            else do
                cataDat <- mkCatamorphism tn
                let thisBundle = TyFixerDataBundle constructorData destructorData cataDat
                pure $ M.insert tn thisBundle acc
