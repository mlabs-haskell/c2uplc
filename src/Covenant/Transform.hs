{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform (transformASG) where

import Covenant.ExtendedASG (MonadASG (getASG))
import Covenant.Transform.Pipeline.Common
  ( CodeGenData,
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
