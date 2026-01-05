{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.FirstPass (firstPass) where

import Data.Map (Map)
import Data.Map qualified as M



import Covenant.ASG (
    ASGNode (ACompNode, AnError),
    Ref (AnArg),
 )
import Covenant.Type (
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    ValT (BuiltinFlat),
    tyvar,
 )

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (ix0)
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (LamInternal))
import Data.Kind (Type)


import Covenant.ExtendedASG
import Covenant.Transform.Common
import Data.Row.Records (Rec, (.+), (.==))
import Covenant.Transform.Pipeline.Common

-- From here on out the top level node CANNOT BE ASSUMED TO BE THE HIGHEST NODE NUMERICALLY.
-- This is annoying but there really isn't a sensible way around it.
--
-- We also have to remember to "catch" the IDs for these functions during codegen
-- since they won't have a body, so we're going to have to keep the map around for a while too.
firstPass :: forall (m :: Type -> Type). (MonadASG m) => m (Rec FirstPassMeta)
firstPass = do
    uniqueErrorId <- ephemeralErrorId
    identityId <- mkIdentityFn
    eInsert uniqueErrorId AnError
    polyRepHandlers <- M.unions <$> traverse (mkRepHandler uniqueErrorId) [IntegerT, ByteStringT]
    pure $
        #builtinHandlers .== polyRepHandlers
            .+ #identityFn .== identityId
            .+ #uniqueError .== uniqueErrorId
  where
    mkRepHandler :: ExtendedId -> BuiltinFlatT -> m (Map BuiltinFlatT PolyRepHandler)
    mkRepHandler errId t = do
        projT <- projectionId
        embedT <- embeddingId
        let synthFnTy = Comp0 $ BuiltinFlat t :--:> ReturnT (BuiltinFlat t)
            synthFnNode = syntheticLamNode (UniqueError . forgetExtendedId $ errId) synthFnTy
        eInsert projT synthFnNode
        eInsert embedT synthFnNode
        pure $ M.singleton t (PolyRepHandler (forgetExtendedId projT) (forgetExtendedId embedT))

    mkIdentityFn :: m ExtendedId
    mkIdentityFn = do
        idFnId <- identityFnId
        let compNode = ACompNode (Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) (LamInternal (AnArg (UnsafeMkArg Z ix0 (tyvar Z ix0))))
        eInsert idFnId compNode
        pure idFnId
