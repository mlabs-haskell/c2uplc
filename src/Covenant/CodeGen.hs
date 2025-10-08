
module Covenant.CodeGen where

import Covenant.Type
import Covenant.Type qualified as T
import Covenant.ASG
import Covenant.Data
import Covenant.Constant
import Covenant.Prim (OneArgFunc(..),TwoArgFunc(..),ThreeArgFunc(..),SixArgFunc(..))

import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS (RWS)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, modify, gets)
import Control.Monad.Error.Class

import Data.Foldable (foldl')

import Data.Kind(Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Word (Word64)

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Data.Text (Text)

import Optics.Core (set, over, view, (%))

import Covenant.MockPlutus

data CodeGenError
  = NoASG
  | TermNotInContext Id
  | NoDatatype TyName
  | ConstructorNotInDatatype TyName ConstructorName
  | InvalidOpaqueEncoding Text



newtype CodeGenM a = CodeGenM (ExceptT CodeGenError (RWS (Map TyName (DatatypeInfo AbstractTy)) () (Map Id PlutusTerm)) a)
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadReader (Map TyName (DatatypeInfo AbstractTy)),
      MonadState (Map Id PlutusTerm),
      MonadError CodeGenError
    ) via (ExceptT CodeGenError (RWS (Map TyName (DatatypeInfo AbstractTy)) () (Map Id PlutusTerm)))

lookupTerm :: Id -> CodeGenM PlutusTerm
lookupTerm i = gets (M.lookup i) >>= \case
  Nothing -> throwError $ TermNotInContext i
  Just term -> pure term

lookupDatatype :: TyName -> CodeGenM (DatatypeInfo AbstractTy)
lookupDatatype tn = asks (M.lookup tn) >>= \case
  Nothing -> throwError $ NoDatatype tn

generatePLC :: [(Id,ASGNode)] -> CodeGenM PlutusTerm
generatePLC = \case
  [] -> throwError NoASG
  ((i,n):rest) -> go i n rest
 where
   go :: Id -> ASGNode -> [(Id,ASGNode)] -> CodeGenM PlutusTerm
   go i node rest = case rest of
     [] -> nodeToTerm node
     ((i',node'):rest') -> do
       let letBindable = countOccurs i (node:map snd rest) > 1
       thisTerm <- nodeToTerm node
       if letBindable
         then do
           modify $ M.insert i thisTerm
           go i' node' rest'
         else do
           let iName = idName i
           let iVar = pVar iName
           modify $ M.insert i iVar
           termInner <- go i' node' rest'
           pure $ pLam iName termInner `pApp` thisTerm


nodeToTerm :: ASGNode -> CodeGenM PlutusTerm
nodeToTerm = \case
  ACompNode compTy compNodeInfo -> case compNodeInfo of
    Builtin1 bi1 -> pure $ pBuiltin (SomeBuiltin1 bi1)
    Builtin2 bi2 -> pure $ pBuiltin  (SomeBuiltin2 bi2)
    Builtin3 bi3 -> pure $ pBuiltin  (SomeBuiltin3 bi3)
    Builtin6 bi6 -> pure $ pBuiltin (SomeBuiltin6 bi6)
    Force r      -> forceToTerm r
    Lam r -> lamToTerm compTy r
  AValNode valT valNodeInfo -> case valNodeInfo of
    Lit aConstant -> litToTerm aConstant
    App i args _ -> do
      fTerm <- lookupTerm i
      resolvedArgs <- traverse refToTerm args
      pure $ foldl' pApp fTerm resolvedArgs
    Thunk i -> thunkToTerm i
    Cata alg val -> cataToTerm alg val
    DataConstructor tn cn fields -> dataConToTerm tn cn fields
    Match scrut handlers -> matchToTerm scrut handlers

matchToTerm :: Ref -> Vector Ref -> CodeGenM PlutusTerm
matchToTerm = undefined

dataConToTerm :: TyName -> ConstructorName -> Vector Ref -> CodeGenM PlutusTerm
dataConToTerm tn cn@(ConstructorName rawCName) args = do
  dtInfo <- lookupDatatype tn
  case view #originalDecl dtInfo of
    -- We assume the opaque encoding has been checked
    OpaqueData {} -> case rawCName of
      "PlutusI" -> iData <$> refToTerm (args Vector.! 0)
      "PlutusB" -> bData <$> refToTerm (args Vector.! 0)
      "PlutusConstr" -> do
        termified <- traverse refToTerm args
        let cIx = termified Vector.! 0
            cArgs = termified Vector.! 1
        pure $ constrData cIx cArgs
      "PlutusList" -> listData <$> traverse refToTerm args
      "PlutusMap" -> mapData <$> traverse refToTerm args
      other -> throwError $ InvalidOpaqueEncoding other
    DataDeclaration _ _ ctors encoding -> case encoding of
      SOP -> do
        ctorIx <- getConstructorIndex tn cn ctors
        resolvedArgs <- traverse refToTerm args
        pure $ pConstr ctorIx resolvedArgs
      PlutusData strat ->  -- We are going to assume that the strategy has been checked
        case strat of
          EnumData -> plutus_I <$> getConstructorIndex tn cn ctors
          ProductListData -> pDataList <$> traverse refToTerm args
          T.ConstrData -> do
            cIx <- getConstructorIndex tn cn ctors
            plutus_ConstrData cIx <$> traverse refToTerm args
          NewtypeData  -> refToTerm (Vector.head args)


getEncoding :: DatatypeInfo AbstractTy ->  DataEncoding
getEncoding = view (#originalDecl % #datatypeEncoding)

getConstructorIndex :: forall (n :: Type)
                     . Num n
                    => TyName
                    -> ConstructorName
                    -> Vector (Constructor AbstractTy)
                    -> CodeGenM n
getConstructorIndex tn cn ctors  = case  Vector.findIndex (\x -> view #constructorName x == cn) ctors of
  Nothing -> throwError $ ConstructorNotInDatatype tn cn
  Just cIx -> pure $ fromIntegral cIx

cataToTerm :: Ref -> Ref -> CodeGenM PlutusTerm
cataToTerm = undefined

thunkToTerm :: Id -> CodeGenM PlutusTerm
thunkToTerm = undefined

litToTerm :: AConstant -> CodeGenM PlutusTerm
litToTerm = undefined

lamToTerm :: CompT AbstractTy -> Ref -> CodeGenM PlutusTerm
lamToTerm = undefined

forceToTerm :: Ref -> CodeGenM PlutusTerm
forceToTerm = undefined



-- NOTE: I am not sure that we can write this function as things currently stand.
--       We need some kind of naming scheme for arguments (which otherwise don't have name)
refToTerm :: Ref -> CodeGenM PlutusTerm
refToTerm = undefined

countOccurs :: Id -> [ASGNode] -> Int
countOccurs = undefined
