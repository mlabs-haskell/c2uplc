{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.FirstPass where

import Data.Map (Map)
import Data.Map qualified as M

import Covenant.ASG (
    ASGNode (ACompNode, AnError),
    Ref (AnArg),
 )
import Covenant.Type (
    AbstractTy,
    BuiltinFlatT (BLS12_381_G1_ElementT, BLS12_381_G2_ElementT, BoolT, ByteStringT, IntegerT, StringT, UnitT),
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    TyName,
    ValT (BuiltinFlat, Datatype),
    tyvar,
 )

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (ix0)
import Covenant.Test (Arg (UnsafeMkArg), CompNodeInfo (LamInternal), Id, list, unsafeMkDatatypeInfos)
import Data.Kind (Type)

import Covenant.ExtendedASG
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Data.Row.Records (Rec, (.+), (.==))

import Covenant.ArgDict
import Covenant.Data (DatatypeInfo)
import Covenant.MockPlutus
import Covenant.Prim (OneArgFunc (IData, ListData, UnIData, UnListData))
import Covenant.Universe

-- import Debug.Trace (traceM)
import PlutusCore.Data (Data (I, List))
import PlutusCore.Default (DefaultUni (..), Esc)
import PlutusCore.MkPlc (mkConstant, mkConstantOf)

import Control.Monad.RWS.Strict (MonadReader (ask), modify')
import Covenant.CodeGen.Stubs
import Covenant.Transform.Pipeline.Monad
import Data.Text (Text)
import Data.Void (Void)
import UntypedPlutusCore (Name)

{- Mainly what this does is to ensure that all of the "primitive" projection/embedding functions
   (which means: for everything except List) have corresponding dummy nodes in the ASG.

   We will have to insert handlers for statically known "compound" projection/embeddings (i.e. for statically
   known concrete list types) during compilation of intro/elim/cata.
-}

-- The ValT is the type *of the thing being projected* not of the *projection function* or anything like that.

firstPass :: PassM Void Datatypes RepPolyHandlers ()
firstPass = do
    uniqueErrorId <- stubId "error"
    let eid = EphemeralError uniqueErrorId
    eInsert eid AnError
    mapM_ (uncurry (bindPrimStub eid)) ((Proj,) <$> primTypes)
    mapM_ (uncurry (bindPrimStub eid)) ((Embed,) <$> primTypes)
  where
    primTypes :: [ValT AbstractTy]
    primTypes = [intT, boolT, stringT, byteStringT, unitT, blsG1T, blsG2T]
    intT = BuiltinFlat IntegerT
    boolT = BuiltinFlat BoolT
    stringT = BuiltinFlat StringT
    byteStringT = BuiltinFlat ByteStringT
    unitT = BuiltinFlat UnitT
    blsG1T = BuiltinFlat BLS12_381_G1_ElementT
    blsG2T = BuiltinFlat BLS12_381_G2_ElementT
    -- Pairs and Map are weird because the types "lie" (the args to Pair are "as if it were data encoded", i.e., they are
    -- Data internally and get projected by *matching on the pair*.)

    bindPrimStub :: ExtendedId -> HandlerType -> ValT AbstractTy -> PassM Void Datatypes RepPolyHandlers ()
    bindPrimStub errId htype ty =
        ask >>= \(Datatypes dtDict) ->
            trySelectHandler dtDict htype ty >>= \case
                Nothing -> error $ "Error in First Pass: Could not locate a " <> show htype <> " handler for " <> show ty
                Just handlerTerm -> do
                    let fnTy = Comp0 $ ty :--:> ReturnT ty
                        synthNode = syntheticLamNode (UniqueError . forgetExtendedId $ errId) fnTy
                    fnId <- case htype of
                        Proj -> projectionId
                        Embed -> embeddingId
                    modify' $ \(RepPolyHandlers byId byTy nilFixers) ->
                        RepPolyHandlers
                            (M.insert (forgetExtendedId fnId) (handlerTerm, htype, ty) byId)
                            (M.insert (ty, htype) (forgetExtendedId fnId) byTy)
                            nilFixers
                    eInsert fnId synthNode
