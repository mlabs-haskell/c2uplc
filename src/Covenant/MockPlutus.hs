{-# LANGUAGE GADTs #-}

module Covenant.MockPlutus where

import Covenant.Constant (AConstant)
import Data.Vector (Vector)
import Covenant.Prim (OneArgFunc, TwoArgFunc, ThreeArgFunc, SixArgFunc)
import Data.Word (Word64)
import Covenant.ASG (Id)

-- mock Plutus types and placeholder helpers
data PlutusTerm

data Name

pVar :: Name -> PlutusTerm
pVar = undefined

pLam :: Name -> PlutusTerm -> PlutusTerm
pLam = undefined

pApp :: PlutusTerm -> PlutusTerm -> PlutusTerm
pApp = undefined

pForce :: PlutusTerm -> PlutusTerm
pForce = undefined

pDelay :: PlutusTerm -> PlutusTerm
pDelay = undefined

pConstant :: AConstant -> PlutusTerm
pConstant = undefined

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

pError :: PlutusTerm
pError = undefined

pConstr :: Word64 -> Vector PlutusTerm -> PlutusTerm
pConstr = undefined

pCase :: PlutusTerm -> Vector PlutusTerm -> PlutusTerm
pCase = undefined

idName :: Id -> Name
idName = undefined
