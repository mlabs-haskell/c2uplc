{-# LANGUAGE GADTs #-}

{- HLINT ignore "Use camelCase" -}

module Covenant.MockPlutus (
    PlutusTerm,
    pVar,
    pLam,
    pApp,
    pForce,
    pDelay,
    pError,
    pConstant,
    pConstr,
    plutus_I,
    plutus_ConstrData,
    pDataList,
    iData,
    bData,
    constrData,
    listData,
    mapData,
    SomeBuiltin (..),
    pBuiltin,
    pCase,
    idName,
) where

import Covenant.Constant (AConstant)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Test (Id (UnsafeId))
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Word (Word64)
import PlutusCore (Name)
import PlutusCore.Default (Some, ValueOf)
import UntypedPlutusCore (DefaultFun, DefaultUni, Term (Apply, Constant, Constr, Delay, Error, Force, LamAbs, Var))

-- mock Plutus types and placeholder helpers
type PlutusTerm = Term Name DefaultUni DefaultFun ()

pVar :: Name -> PlutusTerm
pVar = Var ()

pLam :: Name -> PlutusTerm -> PlutusTerm
pLam = LamAbs ()

pApp :: PlutusTerm -> PlutusTerm -> PlutusTerm
pApp = Apply ()

pForce :: PlutusTerm -> PlutusTerm
pForce = Force ()

pDelay :: PlutusTerm -> PlutusTerm
pDelay = Delay ()

pError :: PlutusTerm
pError = Error ()

pCase :: PlutusTerm -> Vector PlutusTerm -> PlutusTerm
pCase = undefined

pConstant :: AConstant -> PlutusTerm
pConstant = Constant () . constantHelper
  where
    constantHelper :: AConstant -> Some (ValueOf DefaultUni)
    constantHelper = error "TODO (need to track down the module in Plutus w/ the functions I need)"

pConstr :: Word64 -> Vector PlutusTerm -> PlutusTerm
pConstr w = Constr () w . Vector.toList

-- NOTE: I totally forget how you construct data values with PLC functions...
plutus_I :: Integer -> PlutusTerm
plutus_I = undefined

-- Fill in w/ whatever makes the `Constr` branch of PlutusData
plutus_ConstrData :: Integer -> Vector PlutusTerm -> PlutusTerm
plutus_ConstrData = undefined

-- The terms should be data-encoded things
pDataList :: Vector PlutusTerm -> PlutusTerm
pDataList = undefined

-- these _Data functions probably correspond to builtins, I'll look up their names later
-- NOTE: I guess we could do these in the ASG by applying a builtin function.
--       That might be easier than doing it in Plutus. Not sure.
-- 'I'
iData :: PlutusTerm -> PlutusTerm
iData = undefined

-- 'B'
bData :: PlutusTerm -> PlutusTerm
bData = undefined

-- 'Constr' (The data one )
constrData :: PlutusTerm -> PlutusTerm -> PlutusTerm
constrData = undefined

listData :: Vector PlutusTerm -> PlutusTerm
listData = undefined

mapData :: Vector PlutusTerm -> PlutusTerm
mapData = undefined

data SomeBuiltin where
    SomeBuiltin1 :: OneArgFunc -> SomeBuiltin
    SomeBuiltin2 :: TwoArgFunc -> SomeBuiltin
    SomeBuiltin3 :: ThreeArgFunc -> SomeBuiltin
    SomeBuiltin6 :: SixArgFunc -> SomeBuiltin

pBuiltin :: SomeBuiltin -> PlutusTerm
pBuiltin = undefined

idName :: Id -> Name
idName (UnsafeId _i) = undefined
