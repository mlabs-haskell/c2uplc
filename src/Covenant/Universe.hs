{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Universe
  ( UniProof (..),
    ListProof (..),
    analyzeListTy,
    unsafeReflect,
  )
where

import Covenant.Data (DatatypeInfo)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (PlutusData),
    TyName,
    ValT (BuiltinFlat, Datatype),
  )
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Vector qualified as V
import Optics.Core (view)
import PlutusCore.Default
  ( DefaultUni
      ( DefaultUniApply,
        DefaultUniBLS12_381_G1_Element,
        DefaultUniBLS12_381_G2_Element,
        DefaultUniBLS12_381_MlResult,
        DefaultUniBool,
        DefaultUniByteString,
        DefaultUniData,
        DefaultUniInteger,
        DefaultUniProtoList,
        DefaultUniProtoPair,
        DefaultUniString,
        DefaultUniUnit
      ),
    Esc,
  )

{- An existentially quantified GADT witness of default universe membership.

   NOTE: The kind annotation is necessary and MUST be `Type`.
-}
data UniProof :: Type where
  MkUniProof :: forall (a :: Type). DefaultUni (Esc a) -> UniProof

data ListProof :: Type where
  MkListProof :: forall (a :: Type). DefaultUni (Esc [a]) -> ListProof

-- Don't use it on anything that might be a Vector. Though IDK why the hell anyone ever would
unsafeReflect :: forall (a :: Type) (b :: Type). DefaultUni (Esc a) -> ValT b
unsafeReflect = \case
  DefaultUniInteger -> BuiltinFlat IntegerT
  DefaultUniByteString -> BuiltinFlat ByteStringT
  DefaultUniString -> BuiltinFlat StringT
  DefaultUniUnit -> BuiltinFlat UnitT
  DefaultUniBool -> BuiltinFlat BoolT
  DefaultUniData -> Datatype "Data" []
  DefaultUniBLS12_381_MlResult -> BuiltinFlat BLS12_381_MlResultT
  DefaultUniBLS12_381_G1_Element -> BuiltinFlat BLS12_381_G1_ElementT
  DefaultUniBLS12_381_G2_Element -> BuiltinFlat BLS12_381_G2_ElementT
  DefaultUniApply DefaultUniProtoList t -> Datatype "List" [unsafeReflect t]
  DefaultUniApply (DefaultUniApply DefaultUniProtoPair a) b -> Datatype "Pair" [unsafeReflect a, unsafeReflect b]
  other -> error $ "Oops! You misued usafeReflect. It probably shouldn't be used on things like: " <> show other

{- Takes a dictionary containing type information (to look up encodings) and a value type,
   and returns a proof that the equivalent Plutus type is a member of the default Plutus universe
   (if such a proof can be constructed).

   The proofs for builtin types are trivial and are constructed in the obvious way.

   For datatypes:
     - If the datatype has a PlutusData encoding, we can assume that it is Data.
     - If it is an Opaque, we can assume that it is Data.
     - For BuiltinStrategy encoded types:
       - List/Pair use the equivalent DefaultUni witnesses
       - Data (obviously) uses the Data witness
       - Map uses a (List (Pair k v)) witness.
     - We can't construct a witness for anything else.
-}
decideUniType :: Map TyName (DatatypeInfo AbstractTy) -> ValT AbstractTy -> Maybe UniProof
decideUniType dtDict = \case
  BuiltinFlat bi -> case bi of
    IntegerT -> Just $ MkUniProof DefaultUniInteger
    ByteStringT -> Just $ MkUniProof DefaultUniByteString
    StringT -> Just $ MkUniProof DefaultUniByteString
    UnitT -> Just $ MkUniProof DefaultUniUnit
    BoolT -> Just $ MkUniProof DefaultUniBool
    BLS12_381_G1_ElementT -> Just $ MkUniProof DefaultUniBLS12_381_G1_Element
    BLS12_381_G2_ElementT -> Just $ MkUniProof DefaultUniBLS12_381_G2_Element
    BLS12_381_MlResultT -> Just $ MkUniProof DefaultUniBLS12_381_MlResult
  Datatype tn (V.toList -> args)
    | hasDataEncoding tn -> Just $ MkUniProof DefaultUniData
    | otherwise -> case tn of
        "List" -> case args of
          [listElTy] -> do
            MkUniProof listElProof <- decideUniType dtDict listElTy
            pure . MkUniProof $ DefaultUniApply DefaultUniProtoList listElProof
          _ -> Nothing
        "Pair" -> case args of
          [pairA, pairB] -> do
            MkUniProof proofA <- decideUniType dtDict pairA
            MkUniProof proofB <- decideUniType dtDict pairB
            pure . MkUniProof $ DefaultUniApply DefaultUniProtoPair proofA `DefaultUniApply` proofB
          _ -> Nothing
        "Data" -> pure . MkUniProof $ DefaultUniData
        -- I am not sure if we even really need this, but just in case..
        "Map" -> case args of
          [k, v] -> do
            MkUniProof proofK <- decideUniType dtDict k
            MkUniProof proofV <- decideUniType dtDict v
            pure $
              MkUniProof $
                DefaultUniApply DefaultUniProtoList $
                  DefaultUniApply DefaultUniProtoPair proofK `DefaultUniApply` proofV
          _ -> Nothing
        _ -> Nothing
  _ -> Nothing
  where
    hasDataEncoding :: TyName -> Bool
    hasDataEncoding tn = case view #originalDecl <$> M.lookup tn dtDict of
      Nothing -> False
      Just OpaqueData {} -> True
      Just (DataDeclaration _ _ _ enc) -> case enc of
        PlutusData _ -> True
        _ -> False

{- This expect a List ValT and will return nothing if given anything else.

   It constructs a witness for the original type and then peels off the List layers
   to get a witness of the inner universe type and an Int representing the number of layers peeled off.

   We need something like this to facilitiate list projections and embeddings.

   TODO: Better errors than "String"

-}
analyzeListTy ::
  Map TyName (DatatypeInfo AbstractTy) ->
  ValT AbstractTy ->
  Maybe (Integer, UniProof)
analyzeListTy dtDict valT = case decideUniType dtDict valT of
  Nothing -> Nothing
  Just (MkUniProof hopefullyAList) -> go hopefullyAList
  where
    go :: forall (a :: Type). DefaultUni (Esc a) -> Maybe (Integer, UniProof)
    go = \case
      DefaultUniApply DefaultUniProtoList t -> case go t of
        Nothing -> Just (0, MkUniProof t)
        Just (acc, t') -> Just (1 + acc, t')
      _ -> Nothing
