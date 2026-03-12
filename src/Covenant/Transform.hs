{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform (transformASG) where

import Covenant.ExtendedASG (MonadASG (getASG)) -- , unExtendedASG)
import Covenant.Transform.Pipeline.Common (
    CodeGenData,
    ConcretifyCxt,
    TransformState,
 )
import Covenant.Transform.Pipeline.ElimTyFixers (transformTypeFixerNodes)
import Covenant.Transform.Pipeline.FirstPass (firstPass)
import Covenant.Transform.Pipeline.MkTyFixerFnData (mkTypeFixerFnData)
import Covenant.Transform.Pipeline.Monad (CodeGen, Datatypes, initRepPolyHandlers, runPassNoErrors)
import Covenant.Transform.Pipeline.ResolveRepPoly (resolveRepPoly)
import Data.Map qualified as M
import Data.Row.Records (Rec, (.+), (.==))
import Data.Row.Records qualified as R
import Data.Set qualified as S
import Data.Vector qualified as Vector

-- import Debug.Trace (traceM)
-- import Covenant.ArgDict (crudePrettyASG')

transformASG :: Datatypes -> CodeGen (Rec CodeGenData)
transformASG dtDict = do
    (tyFixerData, repPolyHandlers) <- runPassNoErrors dtDict initRepPolyHandlers $ do
        firstPass
        mkTypeFixerFnData
    _ <- getASG
    let transformState :: Rec TransformState
        transformState =
            #visited .== S.empty
                .+ #tyFixerData .== tyFixerData
                .+ #tyFixers .== M.empty

    asgBundle1 <- snd <$> runPassNoErrors dtDict transformState transformTypeFixerNodes
    traceASG "anf"
    let initConcretifyCxt :: Rec ConcretifyCxt
        initConcretifyCxt =
            #context .== M.empty
                .+ #callPath .== Vector.empty
                .+ #appPath .== Vector.empty
                .+ #tyFixers .== (asgBundle1 R..! #tyFixers)
                .+ #datatypes .== dtDict
    finalRepHandlers <- snd <$> runPassNoErrors initConcretifyCxt repPolyHandlers resolveRepPoly
    let codeGenData =
            #tyFixerData .== tyFixerData
                .+ #tyFixers .== (initConcretifyCxt R..! #tyFixers) -- these shouldn't change
                .+ #repPolyHandlers .== finalRepHandlers
    pure codeGenData

traceASG :: (MonadASG m) => String -> m ()
traceASG _msg = pure () {- do
                        asg <- snd . unExtendedASG <$> getASG
                        traceM "--------------"
                        traceM msg
                        traceM $ crudePrettyASG' (M.fromList asg)
                        -}
