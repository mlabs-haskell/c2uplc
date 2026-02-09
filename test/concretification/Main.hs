{-# LANGUAGE OverloadedLists #-}
-- TODO: Once tests are wired this should be removed
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Covenant.ASG
  ( ASG,
    ASGBuilder,
    CovenantError,
    Id,
    Ref (AnArg, AnId),
    app',
    arg,
    builtin2,
    builtin3,
    ctor',
    defaultDatatypes,
    force,
    lam,
    lazyLam,
    lit,
    match,
    runASGBuilder,
  )
import Covenant.Constant (AConstant (ABoolean, AnInteger))
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (ix0, ix1, ix2)
import Covenant.Prim (ThreeArgFunc (IfThenElse), TwoArgFunc (EqualsInteger))
import Covenant.Test (concretifyMegaTest)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (IntegerT),
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    ValT (BuiltinFlat, ThunkT),
    boolT,
    tyvar,
  )

main :: IO ()
main = case debugTest hiddenConcretificationTest of
  Left err -> error (show err)
  Right asg -> print asg

-- FIXME: The maybe here *really* should be `Either`, we might not get "enough rigids" here for this to be useful w Maybe,
--        but it's easier to start w/ maybe and get that compiling then switch over
{-

Need a good test case that involves a mixture of:
  1. Monomorphic non-top-level functions
  2. At least one polymorphic function with a single call site that immediately concretifies it
  3. At least one polymorphic function with a "chain of rigids" (should have a "length > 1" to test everything adequately)
  4. Variants of 2) and 3) that ensure we have adequate coverage of both intro and elim forms

testFn :: Int -> Bool -> Int
testFn i b =
  let fMono :: Bool -> Int
      fMono b = if b then 1 else 0

      gMono :: Int -> Bool
      gMono i = if i == 0 then False else True

      id :: forall a. a -> a
      id x = x

      monoConst :: forall a. a -> a -> a
      monoConst _ y = y

      fPolyOneIntro :: forall a b. (b -> a) -> (a -> a -> a) -> (a -> Bool) -> a -> b -> Maybe a
      fPolyOneIntro fba faa predA a b =
        let ba = fba (monoConst b b)
            aaa = monoConst a (faa a ba)
        in if (predA aaa)
           then Nothing
           else Just aaa

      fPolyOneElim :: forall a b. Maybe a -> (a -> Int) -> b -> (b -> Int) -> Int
      fPolyOneElim mabA aToInt b bToInt = case mabA of
        Nothing -> monoConst 0 (bToInt (monoConst False b))
        Just a  -> aToInt a
  in fPolyOneElim (fPolyOneIntro fMono monoConst gMono i b) id b fMono
-}
testFn :: Either CovenantError ASG
testFn = runASGBuilder defaultDatatypes concretifyMegaTest

{- smaller test

f :: Int -> Bool -> Bool
f i b =
  let g :: forall a. a -> Int
      g a = h a

      h :: forall a. a -> Int
      h x = 2

  in (g i) == (g b)
-}

smallerTestFn :: Either CovenantError ASG
smallerTestFn = runASGBuilder defaultDatatypes smallerTest

smallerTest :: ASGBuilder Id
smallerTest = lam topLevelTy $ do
  h <- lam (Comp1 $ tyvar Z ix0 :--:> ReturnT intT) $ AnId <$> lit (AnInteger 2)
  g <- lam (Comp1 $ tyvar Z ix0 :--:> ReturnT intT) $ do
    x <- AnArg <$> arg Z ix0
    AnId <$> app' h [x]
  i <- AnArg <$> arg Z ix0
  b <- AnArg <$> arg Z ix1
  gi <- AnId <$> app' g [i]
  gb <- AnId <$> app' g [b]
  gi #== gb
  where
    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ intT :--:> boolT :--:> ReturnT boolT

(#==) :: Ref -> Ref -> ASGBuilder Ref
x #== y = do
  equals <- builtin2 EqualsInteger
  AnId <$> app' equals [x, y]

{--

Need at least one test where something polymorphic conretifies *immediately* in >1 call sites

f :: Int -> Bool -> Int
f i b =
  let g :: forall a. a -> Int
      g _ = 2

  in g i == g b
--}

noRigidsTestFn :: Either CovenantError ASG
noRigidsTestFn = runASGBuilder defaultDatatypes noRigidsTest

noRigidsTest :: ASGBuilder Id
noRigidsTest = lam topLevelTy $ do
  g <- lam (Comp1 $ tyvar Z ix0 :--:> ReturnT intT) (AnId <$> lit (AnInteger 2))
  i <- AnArg <$> arg Z ix0
  b <- AnArg <$> arg Z ix1
  gi <- AnId <$> app' g [i]
  gb <- AnId <$> app' g [b]
  gi #== gb
  where
    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ intT :--:> boolT :--:> ReturnT boolT

{-

hidden  :: Int -> Bool -> Bool
hidden i b = rigidBinder i id == rigidBinder b boolToInt
  where
        rigidBinder :: forall a. a -> (a -> Int) -> Bool
        rigidBinder x h  =
         let g :: a -> Bool
             g y = h y == 0

             m :: Maybe r1
             m = Just (h x)
         in let f :: Int -> Bool
                f i = case m of
                  Just rX -> g rX
                  Nothing -> i == (h x)
            in f (h x)

-}

debugTest :: forall a. ASGBuilder a -> Either CovenantError ASG
debugTest = runASGBuilder defaultDatatypes

intT :: ValT AbstractTy
intT = BuiltinFlat IntegerT

ifte :: ASGBuilder Id
ifte = lam (Comp1 $ boolT :--:> tyvar Z ix0 :--:> tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) $ do
  cond <- AnArg <$> arg Z ix0
  t <- AnArg <$> arg Z ix1
  f <- AnArg <$> arg Z ix2
  ifThen <- builtin3 IfThenElse
  AnId <$> app' ifThen [cond, t, f]

hiddenConcretification :: Either CovenantError ASG
hiddenConcretification = runASGBuilder defaultDatatypes hiddenConcretificationTest

hiddenConcretificationTest :: ASGBuilder Id
hiddenConcretificationTest = lam topLevelTy $ do
  rigidBinder <- rigidBinderTest
  i <- AnArg <$> arg Z ix0
  b <- AnArg <$> arg Z ix1
  identitee <- lazyLam (Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) $ AnArg <$> arg Z ix0
  boolToInt <- lazyLam (Comp0 $ boolT :--:> ReturnT intT) $ do
    ifThen <- ifte
    cond <- AnArg <$> arg Z ix0
    zero <- AnId <$> lit (AnInteger 0)
    one <- AnId <$> lit (AnInteger 1)
    AnId <$> app' ifThen [cond, one, zero]
  intResult <- AnId <$> app' rigidBinder [i, AnId identitee]
  boolResult <- AnId <$> app' rigidBinder [b, AnId boolToInt]
  AnId <$> (intResult #&& boolResult)
  where
    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ intT :--:> boolT :--:> ReturnT boolT

(#&&) :: Ref -> Ref -> ASGBuilder Id
b1 #&& b2 = do
  ifThen <- ifte
  fawlse <- AnId <$> lit (ABoolean False)
  app' ifThen [b1, b2, fawlse]

rigidBinderTest :: ASGBuilder Id
rigidBinderTest = lam rigidBinderTy $ do
  _ <- lam (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT boolT) $ do
    y <- AnArg <$> arg Z ix0
    h <- arg (S Z) ix1 >>= force . AnArg
    zero <- AnId <$> lit (AnInteger 0)
    hy <- app' h [y]
    AnId hy #== zero
  f <- lam (Comp0 $ intT :--:> ReturnT boolT) $ do
    justHandler <- lazyLam (Comp0 $ tyvar (S (S Z)) ix0 :--:> ReturnT boolT) $ do
      AnId <$> lit (ABoolean False)
    nothingHandler <- lazyLam (Comp0 $ ReturnT boolT) $ do
      AnId <$> lit (ABoolean False)
    x <- AnArg <$> arg (S Z) ix0
    m <- ctor' "Maybe" "Just" [x]
    AnId <$> match (AnId m) [AnId justHandler, AnId nothingHandler]
  zero <- AnId <$> lit (AnInteger 0)
  AnId <$> app' f [zero]
  where
    rigidBinderTy :: CompT AbstractTy
    rigidBinderTy =
      Comp1 $
        tyvar Z ix0
          :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT intT)
          :--:> ReturnT boolT
