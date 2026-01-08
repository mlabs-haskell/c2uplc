{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Transform where

import Control.Monad (foldM)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set qualified as S
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (runRWS)

import Control.Monad.State.Strict (evalState)
import Covenant.Test (unsafeMkDatatypeInfos)

import Covenant.JSON

import Covenant.ExtendedASG
import Data.Row.Records (Rec, (.+), (.==))
import Data.Row.Records qualified as R

import Covenant.ASG (Id)
import Covenant.MockPlutus (PlutusTerm, pBuiltin)
import Covenant.Prim (OneArgFunc (..))
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common (FirstPassMeta, PipelineData, unliftMetaM, type ConcretifyCxt, type TransformState)
import Covenant.Transform.Pipeline.ElimTyFixers (transformTypeFixerNodes)
import Covenant.Transform.Pipeline.FirstPass (firstPass)
import Covenant.Transform.Pipeline.MkTyFixerFnData (mkTypeFixerFnData)
import Covenant.Transform.Pipeline.ResolveRepPoly (resolveRepPoly)
import Covenant.Type

transformASG :: CompilationUnit -> Rec PipelineData
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

    asgBundle1 <- snd <$> unliftMetaM transformState transformTypeFixerNodes
    let initConcretifyCxt :: Rec ConcretifyCxt
        initConcretifyCxt =
            #context .== M.empty
                .+ #callPath .== Vector.empty
                .+ #appPath .== Vector.empty
                .+ #tyFixers .== (asgBundle1 R..! #tyFixers)
                .+ #builtinHandlers .== (firstPassMeta R..! #builtinHandlers)
                .+ #identityFn .== (firstPassMeta R..! #identityFn)
                .+ #uniqueError .== (firstPassMeta R..! #uniqueError)
    transformedASG <- getASG
    let (_, almostFinalASG, _) = runRWS resolveRepPoly initConcretifyCxt transformedASG
    putASG almostFinalASG
    stubs <- mkStubs firstPassMeta
    finalASG <- getASG
    let pipelineData =
            R.update #asg finalASG asgBundle1
                .+ #handlerStubs .== stubs
    pure pipelineData
  where
    extended :: ExtendedASG
    extended = wrapASG asg

-- This actually inserts bodies into our identity fn / projection embed handlers
-- and removes the placeholder error node
mkStubs :: forall m. (MonadASG m) => Rec FirstPassMeta -> m (Map Id PlutusTerm)
mkStubs firstPassData = do
    -- removeEphemeralError (firstPassData R..! #uniqueError)
    polyRepStubs <- foldM cleanupPolyRep M.empty (M.toList $ firstPassData R..! #builtinHandlers)
    cleanupIdentity (firstPassData R..! #identityFn) polyRepStubs
  where
    cleanupPolyRep :: Map Id PlutusTerm -> (BuiltinFlatT, PolyRepHandler) -> m (Map Id PlutusTerm)
    cleanupPolyRep acc (biTy, (PolyRepHandler projId embedId)) = case biTy of
        IntegerT ->
            pure
                . M.insert projId (pBuiltin UnIData)
                . M.insert embedId (pBuiltin IData)
                $ acc
        ByteStringT ->
            pure
                . M.insert projId (pBuiltin UnBData)
                . M.insert embedId (pBuiltin BData)
                $ acc
    cleanupIdentity :: ExtendedId -> Map Id PlutusTerm -> m (Map Id PlutusTerm)
    cleanupIdentity (forgetExtendedId -> i) acc = do
        term <- pFreshLam pure
        pure $ M.insert i term acc
