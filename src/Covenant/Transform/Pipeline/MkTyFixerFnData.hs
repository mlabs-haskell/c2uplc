{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.MkTyFixerFnData
  ( mkTypeFixerFnData,
  )
where

import Control.Monad (foldM)
import Control.Monad.RWS.Strict (MonadReader (ask), MonadState)
import Covenant.CodeGen.Stubs (MonadStub)
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (ix0)
import Covenant.Transform.Cata (mkCatamorphism)
import Covenant.Transform.Common
  ( BuiltinFnData (ByteString_Cata, Integer_Nat_Cata, Integer_Neg_Cata),
    TyFixerDataBundle (TyFixerDataBundle),
    TyFixerFnData (BuiltinTyFixer),
  )
import Covenant.Transform.Elim (mkDestructorFunction)
import Covenant.Transform.Intro (mkConstructorFunctions)
import Covenant.Transform.Pipeline.Monad (Datatypes (Datatypes), RepPolyHandlers)
import Covenant.Type
  ( AbstractTy,
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    TyName,
    ValT (ThunkT),
    byteStringT,
    integerT,
    tyvar,
  )
import Data.Map (Map)
import Data.Map qualified as M

-- We put #Natural / #Negative / ByteString catas in here.
mkTypeFixerFnData ::
  forall m.
  (MonadStub m, MonadReader Datatypes m, MonadState RepPolyHandlers m) =>
  m (Map TyName TyFixerDataBundle)
mkTypeFixerFnData = do
  (Datatypes datatypes) <- ask
  let allTyNames = M.keys datatypes
  (specialTyFixers <>) <$> foldM go M.empty allTyNames
  where
    go :: Map TyName TyFixerDataBundle -> TyName -> m (Map TyName TyFixerDataBundle)
    go acc tn = do
      destructorData <- mkDestructorFunction tn
      constructorData <- mkConstructorFunctions tn
      -- If we have no constructor functions nor match functions, our datatype is 'void' and we can ignore it
      if null destructorData && null constructorData
        then pure acc
        else do
          cataDat <- mkCatamorphism tn
          let thisBundle = TyFixerDataBundle constructorData destructorData cataDat
          pure $ M.insert tn thisBundle acc

specialTyFixers :: Map TyName TyFixerDataBundle
specialTyFixers =
  M.fromList
    [ ("ByteString", bsBundle),
      ("#Natural", naturalBundle),
      ("#Negative", negativeBundle)
    ]
  where
    bsBundle :: TyFixerDataBundle
    bsBundle = TyFixerDataBundle mempty Nothing (Just $ BuiltinTyFixer cataBsTy ByteString_Cata)
      where
        -- forall r. ByteString -> r -> (Int -> r -> r) -> r
        cataBsTy :: CompT AbstractTy
        cataBsTy =
          Comp1 $
            byteStringT
              :--:> tyvar Z ix0
              :--:> ThunkT (Comp0 $ integerT :--:> tyvar (S Z) ix0 :--:> ReturnT (tyvar (S Z) ix0))
              :--:> ReturnT (tyvar Z ix0)

    -- forall r. Integer -> r -> (r -> r) -> r
    cataIntTy :: CompT AbstractTy
    cataIntTy =
      Comp1 $
        integerT
          :--:> tyvar Z ix0
          :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT (tyvar (S Z) ix0))
          :--:> ReturnT (tyvar Z ix0)

    naturalBundle :: TyFixerDataBundle
    naturalBundle = TyFixerDataBundle mempty Nothing (Just $ BuiltinTyFixer cataIntTy Integer_Nat_Cata)

    negativeBundle :: TyFixerDataBundle
    negativeBundle = TyFixerDataBundle mempty Nothing (Just $ BuiltinTyFixer cataIntTy Integer_Neg_Cata)
