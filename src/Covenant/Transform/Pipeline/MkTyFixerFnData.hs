{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.MkTyFixerFnData where

import Covenant.Type (
    AbstractTy,
    BuiltinFlatT,
    TyName,
 )
import Data.Map (Map)
import Data.Map qualified as M

import Covenant.Data (DatatypeInfo)

import Control.Monad (foldM)
import Control.Monad.RWS.Strict (MonadReader (ask), MonadState)
import Covenant.CodeGen.Stubs (MonadStub)
import Covenant.ExtendedASG
import Covenant.Transform.Cata
import Covenant.Transform.Common
import Covenant.Transform.Elim
import Covenant.Transform.Intro
import Covenant.Transform.Pipeline.Common
import Covenant.Transform.Pipeline.Monad (Datatypes (Datatypes), RepPolyHandlers)

mkTypeFixerFnData ::
    forall m.
    (MonadStub m, MonadReader Datatypes m, MonadState RepPolyHandlers m) =>
    m (Map TyName TyFixerDataBundle)
mkTypeFixerFnData = do
    (Datatypes datatypes) <- ask
    let allTyNames = M.keys datatypes
    foldM go M.empty allTyNames
  where
    go :: Map TyName TyFixerDataBundle -> TyName -> m (Map TyName TyFixerDataBundle)
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
