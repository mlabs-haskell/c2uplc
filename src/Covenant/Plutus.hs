{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ViewPatterns #-}

{- HLINT ignore "Use camelCase" -}

module Covenant.Plutus
  ( pVar,
    pLam,
    pApp,
    pForce,
    pDelay,
    pError,
    pLet,
    pConstant,
    pConstr,
    plutus_I,
    plutus_ConstrData,
    iData,
    bData,
    constrData,
    listData,
    mapData,
    SomeBuiltin (..),
    IsBuiltin (..),
    pBuiltin,
    pCase,
    unIData,
    unListData,
    pHead,
    pTail,
    unConstrData,
    caseConstrEnum,
    pFst,
    pSnd,
    (#),
    (#<=),
    (#-),
    (#+),
    (#==),
    (#<),
    (#!),
    pIf,
    pCons,
    pNilData,
    -- temporary
    mkBuiltinCase,
    oneArgFuncs,
    twoArgFuncs,
    threeArgFuncs,
    sixArgFuncs,
    -- for debugging
    betterPrettyPlutus,
    prettyPTerm,
    ppTerm,
  )
where

import Covenant.Constant
  ( AConstant
      ( ABoolean,
        AByteString,
        AString,
        AUnit,
        AnInteger
      ),
  )
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Prim qualified as Prim
import Data.Foldable (foldl')
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Word (Word64)
import PlutusCore (Name, someValue)
import PlutusCore.Data (Data)
import PlutusCore.Default.Builtins qualified as PB
import PlutusCore.MkPlc (mkConstant)
import Prettyprinter
  ( Doc,
    align,
    angles,
    braces,
    encloseSep,
    group,
    hardline,
    hsep,
    line,
    list,
    nest,
    parens,
    pretty,
    punctuate,
    space,
    vcat,
    vsep,
    (<+>),
  )
import UntypedPlutusCore
  ( DefaultFun,
    DefaultUni,
    Name (Name),
    Term
      ( Apply,
        Builtin,
        Case,
        Constant,
        Constr,
        Delay,
        Error,
        Force,
        LamAbs,
        Var
      ),
  )

-- mock Plutus types and placeholder helpers
-- type Term Name DefaultUni DefaultFun () = Term Name DefaultUni DefaultFun ()

pVar :: Name -> Term Name DefaultUni DefaultFun ()
pVar = Var ()

pLam ::
  Name ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
pLam = LamAbs ()

pApp ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
pApp = Apply ()

pLet ::
  Name ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
pLet varNm toBind inner = pLam varNm inner # toBind

-- It just makes things easier to read. Same fixity as plutarch
(#) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
f # a = pApp f a

infixl 8 #

pForce :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
pForce = Force ()

pDelay :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
pDelay = Delay ()

pError :: Term Name DefaultUni DefaultFun ()
pError = Error ()

pCase ::
  Term Name DefaultUni DefaultFun () ->
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
pCase = Case ()

betterPrettyPlutus :: forall ann. Term Name DefaultUni DefaultFun () -> Doc ann
betterPrettyPlutus pt = vcat . reverse $ go [] pt
  where
    go :: [Doc ann] -> Term Name DefaultUni DefaultFun () -> [Doc ann]
    go acc = \case
      Apply () (LamAbs () (Name txt _) body) arg ->
        let here = "let" <+> pretty txt <+> "=" <+> pretty arg <+> space
         in go (here : acc) body
      other -> pretty other : acc

ppTerm :: Term Name DefaultUni DefaultFun () -> String
ppTerm = show . prettyPTerm

prettyPTerm :: forall ann. Term Name DefaultUni DefaultFun () -> Doc ann
prettyPTerm pt = case takeBindable ([], pt) of
  ([], rest) -> prettyNoBind rest
  (letBinds, rest) ->
    let pRest = "in" <+> prettyNoBind rest
     in align . vsep . reverse $ (pRest : letBinds)
  where
    takeBindable :: ([Doc ann], Term Name DefaultUni DefaultFun ()) -> ([Doc ann], Term Name DefaultUni DefaultFun ())
    takeBindable (acc, t) = case t of
      Apply () (LamAbs () (Name txt _) body) arg ->
        let here = "let" <+> pretty txt <+> "=" <+> prettyPTerm arg
         in takeBindable (here : acc, body)
      other -> (acc, other)
    takeLamArgs :: ([Text], Term Name DefaultUni DefaultFun ()) -> ([Text], Term Name DefaultUni DefaultFun ())
    takeLamArgs (varAcc, next) = case next of
      LamAbs () (Name txt _) body -> takeLamArgs (txt : varAcc, body)
      _ -> (reverse varAcc, next)
    prettyNoBind :: Term Name DefaultUni DefaultFun () -> Doc ann
    prettyNoBind = \case
      Var () (Name txt _) -> pretty txt
      LamAbs () (Name txt _) _body ->
        let (vars, body) = takeLamArgs ([txt], _body)
         in align . group $
              "\\" <> hsep (pretty <$> vars) <+> "->" <> line <> nest 2 (prettyPTerm body)
      Apply () f arg ->
        let fs = prettyAtomic <$> analyzeApp f
         in align . group . encloseSep "" "" " # " $ (fs <> [prettyAtomic arg])
      Force () inner -> "!" <> prettyAtomic inner
      Delay () inner -> angles $ prettyNoBind inner
      c@(Constant _ _) -> pretty c
      Builtin _ b -> pretty b
      Error {} -> "ERROR"
      Constr () cix args -> "constr" <+> pretty cix <+> align (group $ list (prettyPTerm <$> args))
      Case () scrut handlers ->
        group $
          "case"
            <+> prettyNoBind scrut
            <+> hardline
            <> align
              ( group
                  (nest 2 . braces . vcat . punctuate ";" . fmap prettyPTerm . Vector.toList $ handlers)
              )
    prettyAtomic :: Term Name DefaultUni DefaultFun () -> Doc ann
    prettyAtomic = \case
      v@Var {} -> prettyNoBind v
      c@Constant {} -> prettyNoBind c
      e@Error {} -> prettyNoBind e
      d@Delay {} -> prettyNoBind d
      f@Force {} -> prettyNoBind f
      b@Builtin {} -> prettyNoBind b
      other -> align . group . parens . prettyNoBind $ other
    analyzeApp :: Term Name DefaultUni DefaultFun () -> [Term Name DefaultUni DefaultFun ()]
    analyzeApp = \case
      Apply () f arg -> analyzeApp f <> [arg]
      other -> [other]

pConstant :: AConstant -> Term Name DefaultUni DefaultFun ()
pConstant = \case
  AUnit -> mkConstant () ()
  ABoolean b -> mkConstant () b
  AnInteger i -> mkConstant () i
  AByteString bs -> mkConstant () bs
  AString txt -> mkConstant () txt

-- | Makes the SOP Constr
pConstr ::
  Word64 ->
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
pConstr w = Constr () w . Vector.toList

plutus_I :: Integer -> Term Name DefaultUni DefaultFun ()
plutus_I i = pBuiltin Prim.IData # mkConstant () i

-- Makes a Constr PlutusData
plutus_ConstrData ::
  Integer ->
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
plutus_ConstrData cix ctorArgs = constrData (mkConstant () cix) (pBuiltinList pNilData ctorArgs)

-- these _Data functions probably correspond to builtins, I'll look up their names later
-- NOTE: I guess we could do these in the ASG by applying a builtin function.
--       That might be easier than doing it in Plutus. Not sure.
-- 'I'
iData :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
iData t = pBuiltin Prim.IData # t

unIData :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
unIData t = pBuiltin Prim.UnIData # t

-- 'B'
bData :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
bData t = pBuiltin Prim.BData # t

-- 'Constr' (The data one)

-- | This exepects a non-data-encoded Integer term for the first arg.
-- TODO Check that that's what we give it anywhere it might be used
constrData :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
constrData cix ctorArgs = pBuiltin Prim.ConstrData # cix # ctorArgs

-- This rips apart a (data) Constr and returns the (Int,[Data]) pair (at the PLC level)
unConstrData :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
unConstrData t = pBuiltin Prim.UnConstrData # t

-- does not apply anything to the handlers
caseConstrEnum ::
  Term Name DefaultUni DefaultFun () ->
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
caseConstrEnum scrut = pCase ctorIx
  where
    ctorIx = pFst (unConstrData scrut)

-- convenience for pApp FstPair
pFst :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
pFst aPair = pBuiltin Prim.FstPair # aPair

-- convenicne for pApp SndPair
pSnd :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
pSnd aPair = pBuiltin Prim.SndPair # aPair

pCons ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
pCons x xs = pBuiltin Prim.MkCons # x # xs

pNilData :: Term Name DefaultUni DefaultFun ()
pNilData = Constant () $ someValue @[Data] []

-- | Uses `case` and not `IfThenElse`
pIf ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
pIf cond t f = pCase cond [f, t]

(#-) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
x #- y =
  let minus = Builtin () PB.SubtractInteger
   in minus # x # y

(#<=) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
x #<= y =
  let lte = Builtin () PB.LessThanEqualsInteger
   in lte # x # y

(#<) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
x #< y = pBuiltin Prim.LessThanInteger # x # y

(#==) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
x #== y = pBuiltin Prim.EqualsInteger # x # y

(#+) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
x #+ y = pBuiltin Prim.AddInteger # x # y

(#!) ::
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun () ->
  Term Name DefaultUni DefaultFun ()
bs #! ix = pBuiltin Prim.IndexByteString # bs # ix

-- This makes a builtin list, not data-wrapped
pBuiltinList ::
  Term Name DefaultUni DefaultFun () ->
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
pBuiltinList = Vector.foldr pCons

-- This makes the PLUTUS DATA LIST (not a builtin list)
listData ::
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
listData els = pBuiltin Prim.ListData # pBuiltinList pNilData els

-- List xs -> xs
unListData :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
unListData t = pBuiltin Prim.UnListData # t

pHead :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
pHead t = pBuiltin Prim.HeadList # t

pTail :: Term Name DefaultUni DefaultFun () -> Term Name DefaultUni DefaultFun ()
pTail t = pBuiltin Prim.TailList # t

mapData ::
  Vector (Term Name DefaultUni DefaultFun ()) ->
  Term Name DefaultUni DefaultFun ()
mapData t = pBuiltin Prim.MapData # pBuiltinList pNilData t

class IsBuiltin t where
  mkBuiltin :: t -> SomeBuiltin

instance IsBuiltin OneArgFunc where
  mkBuiltin = SomeBuiltin1

instance IsBuiltin TwoArgFunc where
  mkBuiltin = SomeBuiltin2

instance IsBuiltin ThreeArgFunc where
  mkBuiltin = SomeBuiltin3

instance IsBuiltin SixArgFunc where
  mkBuiltin = SomeBuiltin6

-- maybe there's something in plutus but writing the class takes way less long
-- than poking around in that mess of NO EXPLICIT IMPORTS
pBuiltin :: forall t. (IsBuiltin t) => t -> Term Name DefaultUni DefaultFun ()
pBuiltin = pMkBuiltin . mkBuiltin

data SomeBuiltin where
  SomeBuiltin1 :: OneArgFunc -> SomeBuiltin
  SomeBuiltin2 :: TwoArgFunc -> SomeBuiltin
  SomeBuiltin3 :: ThreeArgFunc -> SomeBuiltin
  SomeBuiltin6 :: SixArgFunc -> SomeBuiltin

pMkBuiltin :: SomeBuiltin -> Term Name DefaultUni DefaultFun ()
pMkBuiltin = \case
  SomeBuiltin1 bi -> case bi of
    Prim.LengthOfByteString -> Builtin () PB.LengthOfByteString
    Prim.Sha2_256 -> Builtin () PB.Sha2_256
    Prim.Sha3_256 -> Builtin () PB.Sha3_256
    Prim.Blake2b_256 -> Builtin () PB.Blake2b_256
    Prim.EncodeUtf8 -> Builtin () PB.EncodeUtf8
    Prim.DecodeUtf8 -> Builtin () PB.DecodeUtf8
    Prim.FstPair -> pForce $ pForce $ Builtin () PB.FstPair
    Prim.SndPair -> pForce $ pForce $ Builtin () PB.SndPair
    Prim.HeadList -> pForce $ Builtin () PB.HeadList
    Prim.TailList -> pForce $ Builtin () PB.TailList
    Prim.NullList -> pForce $ Builtin () PB.NullList
    Prim.MapData -> Builtin () PB.MapData
    Prim.ListData -> Builtin () PB.ListData
    Prim.IData -> Builtin () PB.IData
    Prim.BData -> Builtin () PB.BData
    Prim.UnConstrData -> Builtin () PB.UnConstrData
    Prim.UnMapData -> Builtin () PB.UnMapData
    Prim.UnListData -> Builtin () PB.UnListData
    Prim.UnIData -> Builtin () PB.UnIData
    Prim.UnBData -> Builtin () PB.UnBData
    Prim.SerialiseData -> Builtin () PB.SerialiseData
    Prim.BLS12_381_G1_neg -> Builtin () PB.Bls12_381_G1_neg
    Prim.BLS12_381_G1_compress -> Builtin () PB.Bls12_381_G1_compress
    Prim.BLS12_381_G1_uncompress -> Builtin () PB.Bls12_381_G1_uncompress
    Prim.BLS12_381_G2_neg -> Builtin () PB.Bls12_381_G2_neg
    Prim.BLS12_381_G2_compress -> Builtin () PB.Bls12_381_G2_compress
    Prim.BLS12_381_G2_uncompress -> Builtin () PB.Bls12_381_G2_uncompress
    Prim.Keccak_256 -> Builtin () PB.Keccak_256
    Prim.Blake2b_224 -> Builtin () PB.Blake2b_224
    Prim.ComplementByteString -> Builtin () PB.ComplementByteString
    Prim.CountSetBits -> Builtin () PB.CountSetBits
    Prim.FindFirstSetBit -> Builtin () PB.FindFirstSetBit
    Prim.Ripemd_160 -> Builtin () PB.Ripemd_160
  SomeBuiltin2 bi -> case bi of
    Prim.AddInteger -> Builtin () PB.AddInteger
    Prim.SubtractInteger -> Builtin () PB.SubtractInteger
    Prim.MultiplyInteger -> Builtin () PB.MultiplyInteger
    Prim.DivideInteger -> Builtin () PB.DivideInteger
    Prim.QuotientInteger -> Builtin () PB.QuotientInteger
    Prim.RemainderInteger -> Builtin () PB.RemainderInteger
    Prim.ModInteger -> Builtin () PB.ModInteger
    Prim.EqualsInteger -> Builtin () PB.EqualsInteger
    Prim.LessThanInteger -> Builtin () PB.LessThanInteger
    Prim.LessThanEqualsInteger -> Builtin () PB.LessThanEqualsInteger
    Prim.AppendByteString -> Builtin () PB.AppendByteString
    Prim.ConsByteString -> Builtin () PB.ConsByteString
    Prim.IndexByteString -> Builtin () PB.IndexByteString
    Prim.EqualsByteString -> Builtin () PB.EqualsByteString
    Prim.LessThanByteString -> Builtin () PB.LessThanByteString
    Prim.LessThanEqualsByteString -> Builtin () PB.LessThanEqualsByteString
    Prim.AppendString -> Builtin () PB.AppendString
    Prim.EqualsString -> Builtin () PB.EqualsString
    Prim.ChooseUnit -> pForce $ Builtin () PB.ChooseUnit
    Prim.Trace -> pForce $ Builtin () PB.Trace
    Prim.MkCons -> pForce $ Builtin () PB.MkCons
    Prim.ConstrData -> Builtin () PB.ConstrData
    Prim.EqualsData -> Builtin () PB.EqualsData
    Prim.MkPairData -> Builtin () PB.MkPairData
    Prim.BLS12_381_G1_add -> Builtin () PB.Bls12_381_G1_add
    Prim.BLS12_381_G1_scalarMul -> Builtin () PB.Bls12_381_G1_scalarMul
    Prim.BLS12_381_G1_equal -> Builtin () PB.Bls12_381_G1_equal
    Prim.BLS12_381_G1_hashToGroup -> Builtin () PB.Bls12_381_G1_hashToGroup
    Prim.BLS12_381_G2_add -> Builtin () PB.Bls12_381_G2_add
    Prim.BLS12_381_G2_scalarMul -> Builtin () PB.Bls12_381_G2_scalarMul
    Prim.BLS12_381_G2_equal -> Builtin () PB.Bls12_381_G2_equal
    Prim.BLS12_381_G2_hashToGroup -> Builtin () PB.Bls12_381_G2_hashToGroup
    Prim.BLS12_381_millerLoop -> Builtin () PB.Bls12_381_millerLoop
    Prim.BLS12_381_mulMlResult -> Builtin () PB.Bls12_381_mulMlResult
    Prim.BLS12_381_finalVerify -> Builtin () PB.Bls12_381_finalVerify
    Prim.ByteStringToInteger -> Builtin () PB.ByteStringToInteger
    Prim.ReadBit -> Builtin () PB.ReadBit
    Prim.ReplicateByte -> Builtin () PB.ReplicateByte
    Prim.ShiftByteString -> Builtin () PB.ShiftByteString
    Prim.RotateByteString -> Builtin () PB.RotateByteString
  SomeBuiltin3 bi -> case bi of
    Prim.VerifyEd25519Signature -> Builtin () PB.VerifyEd25519Signature
    Prim.VerifyEcdsaSecp256k1Signature -> Builtin () PB.VerifyEcdsaSecp256k1Signature
    Prim.VerifySchnorrSecp256k1Signature -> Builtin () PB.VerifySchnorrSecp256k1Signature
    Prim.IfThenElse -> pForce $ Builtin () PB.IfThenElse
    Prim.ChooseList -> pForce $ Builtin () PB.ChooseList
    Prim.IntegerToByteString -> Builtin () PB.IntegerToByteString
    Prim.AndByteString -> Builtin () PB.AndByteString
    Prim.OrByteString -> Builtin () PB.OrByteString
    Prim.XorByteString -> Builtin () PB.XorByteString
    Prim.WriteBits -> Builtin () PB.WriteBits
    Prim.ExpModInteger -> Builtin () PB.ExpModInteger
  SomeBuiltin6 bi6 -> case bi6 of
    Prim.ChooseData -> pForce $ Builtin () PB.ChooseData

mkBuiltinCase :: forall a. (Show a) => Int -> String -> [a] -> String
mkBuiltinCase indent var ctors = "case " <> var <> " of" <> cases
  where
    cases = foldl' go "" ctors
    go :: String -> a -> String
    go acc (show -> ctor) = acc <> "\n" <> replicate indent ' ' <> ctor <> " -> " <> "Builtin () PB." <> ctor

oneArgFuncs :: [OneArgFunc]
oneArgFuncs =
  [ Prim.LengthOfByteString,
    Prim.Sha2_256,
    Prim.Sha3_256,
    Prim.Blake2b_256,
    Prim.EncodeUtf8,
    Prim.DecodeUtf8,
    Prim.FstPair,
    Prim.SndPair,
    Prim.HeadList,
    Prim.TailList,
    Prim.NullList,
    Prim.MapData,
    Prim.ListData,
    Prim.IData,
    Prim.BData,
    Prim.UnConstrData,
    Prim.UnMapData,
    Prim.UnListData,
    Prim.UnIData,
    Prim.UnBData,
    Prim.SerialiseData,
    Prim.BLS12_381_G1_neg,
    Prim.BLS12_381_G1_compress,
    Prim.BLS12_381_G1_uncompress,
    Prim.BLS12_381_G2_neg,
    Prim.BLS12_381_G2_compress,
    Prim.BLS12_381_G2_uncompress,
    Prim.Keccak_256,
    Prim.Blake2b_224,
    Prim.ComplementByteString,
    Prim.CountSetBits,
    Prim.FindFirstSetBit,
    Prim.Ripemd_160
  ]

twoArgFuncs :: [TwoArgFunc]
twoArgFuncs =
  [ Prim.AddInteger,
    Prim.SubtractInteger,
    Prim.MultiplyInteger,
    Prim.DivideInteger,
    Prim.QuotientInteger,
    Prim.RemainderInteger,
    Prim.ModInteger,
    Prim.EqualsInteger,
    Prim.LessThanInteger,
    Prim.LessThanEqualsInteger,
    Prim.AppendByteString,
    Prim.ConsByteString,
    Prim.IndexByteString,
    Prim.EqualsByteString,
    Prim.LessThanByteString,
    Prim.LessThanEqualsByteString,
    Prim.AppendString,
    Prim.EqualsString,
    Prim.ChooseUnit,
    Prim.Trace,
    Prim.MkCons,
    Prim.ConstrData,
    Prim.EqualsData,
    Prim.MkPairData,
    Prim.BLS12_381_G1_add,
    Prim.BLS12_381_G1_scalarMul,
    Prim.BLS12_381_G1_equal,
    Prim.BLS12_381_G1_hashToGroup,
    Prim.BLS12_381_G2_add,
    Prim.BLS12_381_G2_scalarMul,
    Prim.BLS12_381_G2_equal,
    Prim.BLS12_381_G2_hashToGroup,
    Prim.BLS12_381_millerLoop,
    Prim.BLS12_381_mulMlResult,
    Prim.BLS12_381_finalVerify,
    Prim.ByteStringToInteger,
    Prim.ReadBit,
    Prim.ReplicateByte,
    Prim.ShiftByteString,
    Prim.RotateByteString
  ]

threeArgFuncs :: [ThreeArgFunc]
threeArgFuncs =
  [ Prim.VerifyEd25519Signature,
    Prim.VerifyEcdsaSecp256k1Signature,
    Prim.VerifySchnorrSecp256k1Signature,
    Prim.IfThenElse,
    Prim.ChooseList,
    Prim.IntegerToByteString,
    Prim.AndByteString,
    Prim.OrByteString,
    Prim.XorByteString,
    Prim.WriteBits,
    Prim.ExpModInteger
  ]

sixArgFuncs :: [SixArgFunc]
sixArgFuncs = [Prim.ChooseData]
