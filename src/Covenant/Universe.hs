{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Universe where

import Covenant.Data
import Covenant.Type
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import PlutusCore.Default (DefaultUni (..), Esc)

import Data.Vector qualified as V
import Optics.Core (view)

{- An existentially quantified GADT witness of default universe membership.

   NOTE: The kind annotation is necessary and MUST be `Type`.
-}
data UniProof :: Type where
    MkUniProof :: forall (a :: Type). DefaultUni (Esc a) -> UniProof

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
decideUniType dtDict = undefined
