{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform where

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

import Covenant.Transform.Pipeline.Common (type TransformState, type ConcretifyCxt, unliftMetaM)
import Covenant.Transform.Pipeline.ElimTyFixers (transformTypeFixerNodes)
import Covenant.Transform.Pipeline.FirstPass (firstPass)
import Covenant.Transform.Pipeline.MkTyFixerFnData (mkTypeFixerFnData)
import Covenant.Transform.Pipeline.ResolveRepPoly (resolveRepPoly)

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
