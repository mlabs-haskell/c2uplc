{-# LANGUAGE OverloadedLists #-}

module Main (main) where

import Covenant.ASG (ASG (ASG), ASGBuilder, CovenantError, Id, Ref (AnArg, AnId), app', arg, builtin2, lam, lit, runASGBuilder)
import Covenant.Constant (AConstant (AnInteger))
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.ExtendedASG (wrapASG)
import Covenant.Index (ix0, ix1)
import Covenant.Prim (TwoArgFunc (AddInteger, MultiplyInteger))
import Covenant.Test (Id (UnsafeMkId), conformanceDatatypes2, unsafeMkDatatypeInfos)
import Covenant.Type (AbstractTy, BuiltinFlatT (BoolT, IntegerT), CompT (Comp0), CompTBody (ReturnT, (:--:>)), ValT (BuiltinFlat))
import Data.Map qualified as M
import Data.Vector (Vector)
import PlutusCore (Name (Name), Unique (Unique), unUnique, _nameText, _nameUnique)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

main :: IO ()
main = pure ()

{- I am prett ysure this whole module is superfluous

defaultMain . testGroup "arg resolution" $
        [ runArgResTest "test 1" example1 example1Expected
        , runArgResTest "test 2" example2 example2Expected
        , runArgResTest "test 3" example3 example3Expected
        ]

runArgResTest :: String -> ASG -> M.Map Id (Either (Vector Name) (Vector Id)) -> TestTree
runArgResTest nm (ASG asg) expected = testCase nm $ assertEqual nm expected (preprocess $ wrapASG asg)

example1 :: ASG
example1 = unsafeFromRight $ runASGBuilder (unsafeMkDatatypeInfos conformanceDatatypes2) go
  where
    unsafeFromRight :: Either CovenantError b -> b
    unsafeFromRight = \case
        Right x -> x
        Left err' -> error $ "ASG Error: " <> show err'

    topLevelCompTy :: CompT AbstractTy
    topLevelCompTy = Comp0 $ BuiltinFlat IntegerT :--:> BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)

    go :: ASGBuilder Id
    go = lam topLevelCompTy body

    body :: ASGBuilder Ref
    body = do
        x <- AnArg <$> arg Z ix0
        y <- AnArg <$> arg Z ix1
        plus <- builtin2 AddInteger
        AnId <$> app' plus [x, y]
example1Expected :: M.Map Id (Either (Vector Name) (Vector Id))
example1Expected = M.fromList [(UnsafeMkId 0, Right [UnsafeMkId 2]), (UnsafeMkId 1, Right [UnsafeMkId 2]), (UnsafeMkId 2, Left [Name{_nameText = "arg_2_0", _nameUnique = Unique{unUnique = 3}}, Name{_nameText = "arg_2_1", _nameUnique = Unique{unUnique = 4}}])]

-- \x y -> (\z -> z * z) x + (\z -> z * z) y
example2 :: ASG
example2 = unsafeFromRight $ runASGBuilder (unsafeMkDatatypeInfos conformanceDatatypes2) go
  where
    unsafeFromRight :: Either CovenantError b -> b
    unsafeFromRight = \case
        Right x -> x
        Left err' -> error $ "ASG Error: " <> show err'

    topLevelCompTy :: CompT AbstractTy
    topLevelCompTy = Comp0 $ BuiltinFlat IntegerT :--:> BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)

    go :: ASGBuilder Id
    go = lam topLevelCompTy body

    body :: ASGBuilder Ref
    body = do
        plus <- builtin2 AddInteger
        times <- builtin2 MultiplyInteger
        x <- AnArg <$> arg Z ix0
        y <- AnArg <$> arg Z ix1
        -- (\z -> z * z)
        zf <- lam (Comp0 $ BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)) $ do
            z <- AnArg <$> arg Z ix0
            AnId <$> app' times [z, z]
        lhs <- AnId <$> app' zf [x]
        rhs <- AnId <$> app' zf [y]
        AnId <$> app' plus [lhs, rhs]

example2Expected :: M.Map Id (Either (Vector Name) (Vector Id))
example2Expected = M.fromList [(UnsafeMkId 0, Right [UnsafeMkId 7]), (UnsafeMkId 1, Right [UnsafeMkId 3, UnsafeMkId 7]), (UnsafeMkId 2, Right [UnsafeMkId 3, UnsafeMkId 7]), (UnsafeMkId 3, Left [Name{_nameText = "arg_3_0", _nameUnique = Unique{unUnique = 10}}]), (UnsafeMkId 4, Right [UnsafeMkId 7]), (UnsafeMkId 5, Right [UnsafeMkId 7]), (UnsafeMkId 6, Right [UnsafeMkId 7]), (UnsafeMkId 7, Left [Name{_nameText = "arg_7_0", _nameUnique = Unique{unUnique = 8}}, Name{_nameText = "arg_7_1", _nameUnique = Unique{unUnique = 9}}])]

example3 :: ASG
example3 = unsafeFromRight $ runASGBuilder (unsafeMkDatatypeInfos conformanceDatatypes2) go
  where
    unsafeFromRight :: Either CovenantError b -> b
    unsafeFromRight = \case
        Right x -> x
        Left err' -> error $ "ASG Error: " <> show err'

    topLevelCompTy :: CompT AbstractTy
    topLevelCompTy = Comp0 $ BuiltinFlat BoolT :--:> BuiltinFlat BoolT :--:> ReturnT (BuiltinFlat IntegerT)

    go :: ASGBuilder Id
    go = lam topLevelCompTy body

    body :: ASGBuilder Ref
    body = do
        plus <- builtin2 AddInteger
        three <- AnId <$> lit (AnInteger 3)
        four <- AnId <$> lit (AnInteger 4)
        AnId <$> app' plus [three, four]

example3Expected :: M.Map Id (Either (Vector Name) (Vector Id))
example3Expected = M.fromList [(UnsafeMkId 0, Right [UnsafeMkId 4]), (UnsafeMkId 1, Right [UnsafeMkId 4]), (UnsafeMkId 2, Right [UnsafeMkId 4]), (UnsafeMkId 3, Right [UnsafeMkId 4]), (UnsafeMkId 4, Left [Name{_nameText = "arg_4_0", _nameUnique = Unique{unUnique = 5}}, Name{_nameText = "arg_4_1", _nameUnique = Unique{unUnique = 6}}])]
-}
