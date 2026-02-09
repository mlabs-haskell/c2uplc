{-# LANGUAGE OverloadedLists #-}
-- TODO: Once tests are wired up, this should be removed
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{- HLINT ignore "Use camelCase" -}

module Main (main) where

import Covenant.ASG
  ( ASG (ASG),
    ASGBuilder,
    CovenantError (TypeError),
    Id,
    Ref (AnArg, AnId),
    app',
    arg,
    baseFunctorOf,
    builtin2,
    cata,
    ctor,
    ctor',
    lam,
    lazyLam,
    lit,
    match,
    runASGBuilder,
    thunk,
  )
import Covenant.ArgDict (crudePrettyASG, ppASG)
import Covenant.CodeGen (CodeGenError, compile, evalTerm)
import Covenant.Constant
  ( AConstant
      ( ABoolean,
        AByteString,
        AnInteger
      ),
  )
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (count0, count1, ix0, ix1)
import Covenant.JSON (CompilationUnit (CompilationUnit), Version (Version))
import Covenant.Plutus (prettyPTerm)
import Covenant.Prim (TwoArgFunc (AddInteger))
import Covenant.Test (ledgerTypes, list, unsafeMkDatatypeInfos)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT
      ( BoolT,
        IntegerT
      ),
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName,
    DataDeclaration (DataDeclaration),
    DataEncoding (PlutusData, SOP),
    PlutusDataStrategy
      ( ConstrData,
        EnumData,
        NewtypeData,
        ProductListData
      ),
    TyName,
    ValT (BuiltinFlat, Datatype),
    boolT,
    integerT,
    tyvar,
  )
import Data.Bimap (toMap)
import Data.Kind (Type)
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Void (Void)
import Data.Wedge (Wedge (There))
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term)

main :: IO ()
main =
  defaultMain $
    testGroup
      "compilation"
      [ shouldCompile "addTwoNumbers" mempty addTwoNumbers,
        shouldCompile "mkJust_SOP" [maybeSOP] mkJust,
        shouldCompile "mkJust_Data" [maybeData] mkJust,
        shouldCompile "matchMaybeInt_SOP" [maybeSOP] matchOnMaybeInt,
        shouldCompile "matchMaybeInt_Data" [maybeData] matchOnMaybeInt,
        shouldCompile "intro_enum" [abcT] introEnum,
        shouldCompile "elim_enum" [abcT] elimEnum,
        shouldCompile "intro_product_sop" [productSOP] introProduct,
        shouldCompile "intro_product_data" [productData] introProduct,
        shouldCompile "intro_newtype" [myNewtype] introNewtype,
        shouldCompile "elim_newtype" [myNewtype] elimNewtype,
        -- list
        goTest "nil_concrete" mkNilConcrete,
        goTest "cons_concrete" mkConsConcrete,
        goTest "match_list_empty" matchListEmpty,
        goTest "list_cata" cataList,
        -- pair
        goTest "intro_pair" mkPair,
        goTest "elim_pair" matchPair,
        -- data
        goTest "data_I" mkData_I,
        goTest "data_B" mkData_B,
        goTest "data_List" mkData_List,
        goTest "data_Map" mkData_Map,
        goTest "data_constr_1" mkData_Constr_Nullary,
        goTest "data_constr_2" mkData_Constr_Unary,
        -- map
        goTest "intro_map" mkMap,
        goTest "elim_map_1" matchMapEmpty,
        goTest "elim_map_2" matchMapNonEmpty
      ]
  where
    goTest ::
      forall (a :: Type).
      String -> ASGBuilder a -> TestTree
    goTest nm = shouldCompile nm testCxt
    testCxt :: Vector (DataDeclaration AbstractTy)
    testCxt = [dataT, list, pairT, mapT, pairT]

{-
    ******************
    Test Running Utils
    ******************
-}
data CompilerError
  = ASGConstructionFail CovenantError
  | CodeGenFail CodeGenError
  deriving stock (Show)

-- This is for manual debugging of tests that fail
testCompileIO ::
  forall a.
  Vector (DataDeclaration AbstractTy) ->
  ASGBuilder a ->
  IO ()
testCompileIO dtDict builder = case mkASG dtDict builder of
  Left asgErr -> do
    putStrLn $ "!! ERROR !! ASG Construction Fail:\n" <> prettify asgErr
  Right cu@(CompilationUnit _ asg _) -> do
    putStrLn "************************"
    putStrLn "ASG Construction Success"
    putStrLn "************************"
    putStrLn (ppASG asg)
    case compile cu of
      Left cgErr -> putStrLn $ "!! ERROR !! Code gen failed: " <> show cgErr
      Right resTerm -> do
        putStrLn "****************************"
        putStrLn "Code successfully generated!"
        putStrLn "*****************************"
        print (prettyPTerm resTerm)
        putStrLn ""
        putStrLn "Attempting evaluation..."
        putStrLn ""
        case evalTerm resTerm of
          Left err -> putStrLn $ "!! ERROR !! Evaluation failed:\n" <> err
          Right res -> do
            putStrLn "******************"
            putStrLn "Evaluation Success"
            putStrLn "******************"
            print $ prettyPTerm res

prettify :: CovenantError -> String
prettify = \case
  TypeError bimapAsg innerErr ->
    let asgPart = show $ crudePrettyASG (toMap bimapAsg)
        innerErrPart = show innerErr
     in "TypeError\nASG:\n" <> asgPart <> "\nError: " <> show innerErrPart
  other -> show other

-- also evaluates
shouldCompile ::
  forall a.
  String ->
  Vector (DataDeclaration AbstractTy) ->
  ASGBuilder a ->
  TestTree -- i.e. IO (), why do they do that
shouldCompile testNm dtDict builder = testCase testNm $ case testCompile dtDict builder of
  Left err -> assertFailure $ "Compilation failed. Error: " <> err
  Right _ -> pure ()

testCompile ::
  forall a.
  Vector (DataDeclaration AbstractTy) ->
  ASGBuilder a ->
  Either String (Term Name DefaultUni DefaultFun ())
testCompile dtDict builder = case mkASG dtDict builder of
  Left asgErr -> Left $ show (ASGConstructionFail asgErr)
  Right cu -> case compile cu of
    Left cgErr -> Left $ show (CodeGenFail cgErr)
    Right resTerm -> do
      -- traceM $ "\n" <> show (prettyPTerm resTerm) <> "\n"
      case evalTerm resTerm of
        Left errMsg -> Left errMsg
        Right evaluated -> do
          -- traceM $ "\nevaluated:\n" <> show (prettyPTerm evaluated)
          pure evaluated

mkASG ::
  forall a.
  Vector (DataDeclaration AbstractTy) ->
  ASGBuilder a ->
  Either CovenantError CompilationUnit
mkASG dtDict builder = case runASGBuilder (unsafeMkDatatypeInfos $ V.toList dtDict) builder of
  Left err' -> Left err'
  Right (ASG asg) -> do
    pure $ CompilationUnit dtDict asg (Version 0 0)

-- obviously very unsafe and inefficient, but doesn't matter here
ledgerType :: TyName -> DataDeclaration AbstractTy
ledgerType tn =
  fromJust $
    find
      ( \case
          (DataDeclaration tn' _ _ _) -> tn == tn'
          _ -> False
      )
      ledgerTypes

{-
   ************
   Data Declarations & Misc
   ************
-}

-- stuff we pull from the ledger types
dataT :: DataDeclaration AbstractTy
dataT = ledgerType "Data"

pairT :: DataDeclaration AbstractTy
pairT = ledgerType "Pair"

mapT :: DataDeclaration AbstractTy
mapT = ledgerType "Map"

typedNil :: ValT Void -> ASGBuilder Id
typedNil elTy = ctor "List" "Nil" [] [There elTy]

-- parameterized cuz we need to test SOP stuff as well (ledger types are all data)
maybeT :: DataEncoding -> DataDeclaration AbstractTy
maybeT =
  DataDeclaration
    "Maybe"
    count1
    [ Constructor "Nothing" [],
      Constructor "Just" [tyvar Z ix0]
    ]

maybeSOP :: DataDeclaration AbstractTy
maybeSOP = maybeT SOP

maybeData :: DataDeclaration AbstractTy
maybeData = maybeT (PlutusData Covenant.Type.ConstrData)

-- Simple enum type
abcT :: DataDeclaration AbstractTy
abcT =
  DataDeclaration
    "ABC"
    count0
    [ Constructor "A" [],
      Constructor "B" [],
      Constructor "C" []
    ]
    (PlutusData EnumData)

myListT :: DataEncoding -> DataDeclaration AbstractTy
myListT =
  DataDeclaration
    "MyList"
    count1
    [ Constructor "MyNil" [],
      Constructor "MyCons" [tyvar Z ix0, Datatype "MyList" [tyvar Z ix0]]
    ]

myListSOP :: DataDeclaration AbstractTy
myListSOP = myListT SOP

myListData :: DataDeclaration AbstractTy
myListData = myListT (PlutusData Covenant.Type.ConstrData)

-- Simple product type
productT :: DataEncoding -> DataDeclaration AbstractTy
productT =
  DataDeclaration
    "Product"
    count1
    [Constructor "Product" [BuiltinFlat IntegerT, tyvar Z ix0]]

productData :: DataDeclaration AbstractTy
productData = productT (PlutusData ProductListData)

productSOP :: DataDeclaration AbstractTy
productSOP = productT SOP

-- A newtype encoded thing
myNewtype :: DataDeclaration AbstractTy
myNewtype =
  DataDeclaration
    "Newtype"
    count1
    [Constructor "Newtype" [tyvar Z ix0]]
    (PlutusData NewtypeData)

-- TyCon Helpers
pairTy :: ValT a -> ValT a -> ValT a
pairTy a b = Datatype "Pair" [a, b]

dataTy :: forall a. ValT a
dataTy = Datatype "Data" []

listTy :: forall a. ValT a -> ValT a
listTy elTy = Datatype "List" [elTy]

mapTy :: forall a. ValT a -> ValT a -> ValT a
mapTy a b = Datatype "Map" [a, b]

{-
   *****
   Tests
   *****

   NOTE: For types with SOP and Data variants, run the tests with the respective variant to
         test behavior for each encoding.
-}

-- Do simple builtins on integers work?
addTwoNumbers :: ASGBuilder Id
addTwoNumbers = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
  one <- AnId <$> lit (AnInteger 1)
  two <- AnId <$> lit (AnInteger 2)
  plus <- builtin2 AddInteger
  AnId <$> app' plus [one, two]

-- Maybe

mkJust :: ASGBuilder Id
mkJust = lam (Comp0 $ ReturnT (Datatype "Maybe" [BuiltinFlat IntegerT])) $ do
  two <- AnId <$> lit (AnInteger 2)
  AnId <$> ctor' "Maybe" "Just" [two]

matchOnMaybeInt :: ASGBuilder Id
matchOnMaybeInt = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
  zero <- AnId <$> lit (AnInteger 0)
  two <- AnId <$> lit (AnInteger 2)
  just2 <- AnId <$> ctor' "Maybe" "Just" [two]
  plus <- builtin2 AddInteger
  justHandler <- lazyLam (Comp0 $ BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)) $ do
    justWhat <- arg Z ix0
    AnId <$> app' plus [AnArg justWhat, AnArg justWhat]
  AnId <$> match just2 [zero, AnId justHandler]

-- Enumerations

introEnum :: ASGBuilder Id
introEnum = lam (Comp0 $ ReturnT (Datatype "ABC" [])) $ AnId <$> ctor' "ABC" "A" []

elimEnum :: ASGBuilder Id
elimEnum = lam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) $ do
  myABC <- AnId <$> ctor' "ABC" "A" []
  one <- AnId <$> lit (AnInteger 2)
  two <- AnId <$> lit (AnInteger 3)
  three <- AnId <$> lit (AnInteger 4)
  AnId <$> match myABC [one, two, three]

-- Products

introProduct :: ASGBuilder Id
introProduct = lam (Comp0 $ ReturnT (Datatype "Product" [BuiltinFlat BoolT])) $ do
  one <- AnId <$> lit (AnInteger 1)
  fawlse <- AnId <$> lit (ABoolean False)
  AnId <$> ctor' "Product" "Product" [one, fawlse]

-- Newtypes

introNewtype :: ASGBuilder Id
introNewtype = testLam (Datatype "Newtype" [BuiltinFlat IntegerT]) $ do
  one <- AnId <$> lit (AnInteger 1)
  AnId <$> ctor' "Newtype" "Newtype" [one]

elimNewtype :: ASGBuilder Id
elimNewtype = testLam (BuiltinFlat IntegerT) $ do
  one <- AnId <$> lit (AnInteger 1)
  myNT <- AnId <$> ctor' "Newtype" "Newtype" [one]
  idF <- lazyLam (Comp1 $ BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)) $ AnArg <$> arg Z ix0
  AnId <$> match myNT [AnId idF]

-- User defined recursive type
myListInts :: ASGBuilder Id
myListInts = testLam (Datatype "MyList" [BuiltinFlat IntegerT]) $ do
  (one, two, three) <- (,,) <$> lit (AnInteger 1) <*> lit (AnInteger 2) <*> lit (AnInteger 3)
  AnId <$> mkListLike (BuiltinFlat IntegerT) "MyList" "MyCons" "MyNil" [AnId one, AnId two, AnId three]

-- List

mkNilConcrete :: ASGBuilder Id
mkNilConcrete = testLam (Datatype "List" [integerT]) $ do
  AnId <$> ctor "List" "Nil" [] [There integerT]

mkConsConcrete :: ASGBuilder Id
mkConsConcrete = testLam (Datatype "List" [integerT]) $ do
  one <- AnId <$> lit (AnInteger 1)
  nilInt <- AnId <$> ctor "List" "Nil" [] [There integerT]
  AnId <$> ctor' "List" "Cons" [one, nilInt]

-- takes a Ref pointing to a list and
-- matches on the list, returning 0 if Nil and 1 if Cons
-- Note: Expects a [Integer] (since we have to specify due to disallowing polymorphic handlers)
matchList :: Ref -> ASGBuilder Id
matchList ref = testLam integerT $ do
  whenNil <- liftInt 0
  whenCons <- lazyLam (Comp0 $ integerT :--:> listTy integerT :--:> ReturnT integerT) $ liftInt 1
  AnId <$> match ref [whenNil, AnId whenCons]

matchListEmpty :: ASGBuilder Id
matchListEmpty = do
  empty <- typedNil integerT
  matchList (AnId empty)

matchListNonEmpty :: ASGBuilder Id
matchListNonEmpty = do
  zero <- liftInt 0
  nonEmpty <- liftList integerT [zero]
  matchList nonEmpty

cataList :: ASGBuilder Id
cataList = testLam integerT $ do
  listF <- baseFunctorOf "List"
  zero <- liftInt 0
  someInts <- ints [1 .. 5]
  plus <- thunk =<< builtin2 AddInteger
  let algTy = Comp0 $ Datatype listF [integerT] :--:> ReturnT integerT
  AnId <$> cata algTy [zero, AnId plus] someInts

-- Pair

mkPair :: ASGBuilder Id
mkPair = testLam (Datatype "Pair" [integerT, boolT]) $ do
  one <- liftInt 1
  t <- liftBool True
  AnId <$> pair one t

-- sums a pair of integers
matchPair :: ASGBuilder Id
matchPair = testLam integerT $ do
  one <- liftInt 1
  two <- liftInt 2
  aPair <- AnId <$> pair one two
  handler <- lazyLam (Comp0 $ integerT :--:> integerT :--:> ReturnT integerT) $ do
    arg1 <- AnArg <$> arg Z ix0
    arg2 <- AnArg <$> arg Z ix1
    plus <- builtin2 AddInteger
    AnId <$> app' plus [arg1, arg2]
  AnId <$> match aPair [AnId handler]

-- Data

mkData_I :: ASGBuilder Id
mkData_I = testLam (Datatype "Data" []) $ do
  one <- AnId <$> lit (AnInteger 1)
  AnId <$> ctor' "Data" "I" [one]

mkData_B :: ASGBuilder Id
mkData_B = testLam (Datatype "Data" []) $ do
  lol <- AnId <$> lit (AByteString "lolwtfbbq")
  AnId <$> ctor' "Data" "B" [lol]

-- not a test, used as a helper for the next few
listOfData :: ASGBuilder Id
listOfData = do
  one <- liftInt 1
  data_one <- AnId <$> ctor' "Data" "I" [one]
  bs <- AnId <$> lit (AByteString "lolwtfbbq")
  data_bs <- AnId <$> ctor' "Data" "B" [bs]
  mkListLike (Datatype "Data" []) "List" "Cons" "Nil" [data_one, data_bs]

mkData_List :: ASGBuilder Id
mkData_List = testLam (Datatype "Data" []) $ do
  aListOfData <- listOfData
  AnId <$> ctor' "Data" "List" [AnId aListOfData]

mkData_Map :: ASGBuilder Id
mkData_Map = testLam (Datatype "Data" []) $ do
  one <- liftInt 1
  data_one <- AnId <$> ctor' "Data" "I" [one]
  bs <- AnId <$> lit (AByteString "lolwtfbbq")
  data_bs <- AnId <$> ctor' "Data" "B" [bs]
  aListOfPairs <- listOfPairs (dataTy, dataTy) [(data_one, data_bs)]
  AnId <$> ctor' "Data" "Map" [aListOfPairs]

mkData_Constr_Nullary :: ASGBuilder Id
mkData_Constr_Nullary = testLam (Datatype "Data" []) $ do
  zero <- liftInt 0
  emptyDataList <- AnId <$> typedNil dataTy
  AnId <$> ctor' "Data" "Constr" [zero, emptyDataList]

mkData_Constr_Unary :: ASGBuilder Id
mkData_Constr_Unary = testLam (Datatype "Data" []) $ do
  zero <- liftInt 0
  aDataList <- do
    one <- liftInt 1
    oneData <- ctor' "Data" "I" [one]
    liftList dataTy [AnId oneData]
  AnId <$> ctor' "Data" "Constr" [zero, aDataList]

-- Map

mkMap :: ASGBuilder Id
mkMap = testLam (mapTy integerT boolT) $ do
  zero <- liftInt 0
  troo <- liftBool True
  inner <- listOfPairs (integerT, boolT) [(zero, troo)]
  AnId <$> ctor' "Map" "Map" [inner]

-- true if the list arg is nonempty, false if empty
matchMap :: Ref -> ASGBuilder Id
matchMap aMap = testLam boolT $ do
  let mPairTy = pairTy integerT boolT
      mListTy = listTy mPairTy
  matchInner <- lazyLam (Comp0 $ mListTy :--:> ReturnT boolT) $ do
    xs <- AnArg <$> arg Z ix0
    fawlse <- liftBool False
    whenCons <- lazyLam (Comp0 $ mPairTy :--:> mListTy :--:> ReturnT boolT) $ liftBool True
    AnId <$> match xs [fawlse, AnId whenCons]
  AnId <$> match aMap [AnId matchInner]

matchMapEmpty :: ASGBuilder Id
matchMapEmpty = do
  aList <- typedNil (pairTy integerT boolT)
  aMap <- ctor' "Map" "Map" [AnId aList]
  matchMap (AnId aMap)

matchMapNonEmpty :: ASGBuilder Id
matchMapNonEmpty = do
  zero <- liftInt 0
  troo <- liftBool True
  inner <- listOfPairs (integerT, boolT) [(zero, troo)]
  aMap <- AnId <$> ctor' "Map" "Map" [inner]
  matchMap aMap

{-
   *************************
   ASG Level utils & helpers
   ************************
-}
-- helper to reduce clutter
testLam :: ValT AbstractTy -> ASGBuilder Ref -> ASGBuilder Id
testLam retT = lam (Comp0 $ ReturnT retT)

-- helper, not the test (used to construct a few tests)
pair :: Ref -> Ref -> ASGBuilder Id
pair a b = do
  ctor' "Pair" "Pair" [a, b]

mkListLike :: ValT Void -> TyName -> ConstructorName -> ConstructorName -> [Ref] -> ASGBuilder Id
mkListLike listElTy ty _ nil [] = ctor ty nil [] [There listElTy]
mkListLike listElTy ty cons nil (x : xs) = do
  xs' <- AnId <$> mkListLike listElTy ty cons nil xs
  ctor' ty cons [x, xs']

-- saves me a lot of typing, should have done sooner
liftInt :: Integer -> ASGBuilder Ref
liftInt i = AnId <$> lit (AnInteger i)

liftBool :: Bool -> ASGBuilder Ref
liftBool b = AnId <$> lit (ABoolean b)

liftList :: ValT Void -> [Ref] -> ASGBuilder Ref
liftList elTy xs = AnId <$> mkListLike elTy "List" "Cons" "Nil" xs

listOfPairs :: (ValT Void, ValT Void) -> [(Ref, Ref)] -> ASGBuilder Ref
listOfPairs tyPair pairs = do
  somePairs <- traverse (fmap AnId . uncurry pair) pairs
  liftList (uncurry pairTy tyPair) somePairs

ints :: [Integer] -> ASGBuilder Ref
ints xs = do
  xs' <- traverse (fmap AnId . lit . AnInteger) xs
  liftList integerT xs'
