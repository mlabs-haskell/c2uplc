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
import Covenant.ArgDict (crudePrettyASG')
import Covenant.MockPlutus (PlutusTerm, pBuiltin)
import Covenant.Prim (OneArgFunc (..))
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Covenant.Transform.Pipeline.ElimTyFixers (transformTypeFixerNodes)
import Covenant.Transform.Pipeline.FirstPass (firstPass)
import Covenant.Transform.Pipeline.MkTyFixerFnData (mkTypeFixerFnData)
import Covenant.Transform.Pipeline.Monad (CodeGen, Datatypes (Datatypes), initRepPolyHandlers, runPass, runPassNoErrors)
import Covenant.Transform.Pipeline.ResolveRepPoly (resolveRepPoly)
import Covenant.Type

transformASG :: Datatypes -> CodeGen (Rec CodeGenData)
transformASG dtDict = do
    traceASG "initial"
    (tyFixerData, repPolyHandlers) <- runPassNoErrors dtDict initRepPolyHandlers $ do
        firstPass
        mkTypeFixerFnData
    toTransform <- getASG
    traceASG "tyFixersConstructed"
    let transformState :: Rec TransformState
        transformState =
            #visited .== S.empty
                .+ #tyFixerData .== tyFixerData
                .+ #tyFixers .== M.empty

    asgBundle1 <- snd <$> runPassNoErrors dtDict transformState transformTypeFixerNodes
    traceASG "after app transform"
    let initConcretifyCxt :: Rec ConcretifyCxt
        initConcretifyCxt =
            #context .== M.empty
                .+ #callPath .== Vector.empty
                .+ #appPath .== Vector.empty
                .+ #tyFixers .== (asgBundle1 R..! #tyFixers)
                .+ #datatypes .== dtDict
    finalRepHandlers <- snd <$> runPassNoErrors initConcretifyCxt repPolyHandlers resolveRepPoly
    traceM $ "final rep handlers:\n" <> show finalRepHandlers <> "\n"
    traceASG "after rep poly resolution "
    let codeGenData =
            #tyFixerData .== tyFixerData
                .+ #tyFixers .== (initConcretifyCxt R..! #tyFixers) -- these shouldn't change
                .+ #repPolyHandlers .== finalRepHandlers
    pure codeGenData

ppASG :: forall m. (MonadASG m) => m String
ppASG = crudePrettyASG' . M.mapKeys forgetExtendedId . extendedNodes <$> getASG

traceASG :: forall m. (MonadASG m) => String -> m ()
traceASG msg = do
    pasg <- ppASG
    traceM $ msg <> ":" <> "\n" <> pasg <> "\n"

{-
-- This actually inserts bodies into our identity fn / projection embed handlers
-- and removes the placeholder error node
-- NOTE: I don't *think* we need this anymore?
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
-}
