{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ViewPatterns #-}

{- HLINT ignore "Use camelCase" -}

module Covenant.MockPlutus (
    PlutusTerm,
    pVar,
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
) where

import Covenant.Constant (AConstant (..))
import Covenant.Prim
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Test (Id (UnsafeMkId))
import Data.Foldable (foldl')
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Word (Word64)
import PlutusCore (Name, someValue)
import PlutusCore.Data (Data)
import PlutusCore.Default (Some, ValueOf)
import PlutusCore.Default.Builtins qualified as PB
import PlutusCore.MkPlc (mkConstant)
import Prettyprinter
import UntypedPlutusCore (DefaultFun, DefaultUni, Name (..), Term (Apply, Builtin, Case, Constant, Constr, Delay, Error, Force, LamAbs, Var))

-- mock Plutus types and placeholder helpers
type PlutusTerm = Term Name DefaultUni DefaultFun ()

pVar :: Name -> PlutusTerm
pVar = Var ()

pLam :: Name -> PlutusTerm -> PlutusTerm
pLam = LamAbs ()

pApp :: PlutusTerm -> PlutusTerm -> PlutusTerm
pApp = Apply ()

pLet :: Name -> PlutusTerm -> PlutusTerm -> PlutusTerm
pLet varNm toBind inner = pLam varNm inner # toBind

-- It just makes things easier to read. Same fixity as plutarch
(#) :: PlutusTerm -> PlutusTerm -> PlutusTerm
f # a = pApp f a
infixl 8 #

pForce :: PlutusTerm -> PlutusTerm
pForce = Force ()

pDelay :: PlutusTerm -> PlutusTerm
pDelay = Delay ()

pError :: PlutusTerm
pError = Error ()

pCase :: PlutusTerm -> Vector PlutusTerm -> PlutusTerm
pCase = Case ()

betterPrettyPlutus :: forall ann. PlutusTerm -> Doc ann
betterPrettyPlutus pt = vcat . reverse $ go [] pt
  where
    go :: [Doc ann] -> PlutusTerm -> [Doc ann]
    go acc = \case
        Apply () (LamAbs () (Name txt _) body) arg ->
            let here = "let" <+> pretty txt <+> "=" <+> pretty arg <+> space
             in go (here : acc) body
        other -> pretty other : acc

ppTerm :: PlutusTerm -> String
ppTerm = show . prettyPTerm

prettyPTerm :: forall ann. PlutusTerm -> Doc ann
prettyPTerm pt = case takeBindable ([], pt) of
    ([], rest) -> prettyNoBind rest
    (letBinds, rest) ->
        let pRest = "in" <+> prettyNoBind rest
         in align . vsep . reverse $ (pRest : letBinds)
  where
    takeBindable :: ([Doc ann], PlutusTerm) -> ([Doc ann], PlutusTerm)
    takeBindable (acc, t) = case t of
        Apply () (LamAbs () (Name txt _) body) arg ->
            let here = "let" <+> pretty txt <+> "=" <+> prettyPTerm arg
             in takeBindable (here : acc, body)
        other -> (acc, other)

    takeLamArgs :: ([Text], PlutusTerm) -> ([Text], PlutusTerm)
    takeLamArgs (varAcc, next) = case next of
        LamAbs () (Name txt _) body -> takeLamArgs (txt : varAcc, body)
        _ -> (reverse varAcc, next)

    prettyNoBind :: PlutusTerm -> Doc ann
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
        c@(Constant a b) -> pretty c
        bi@(Builtin a b) -> pretty b
        Error{} -> "ERROR"
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

    prettyAtomic :: PlutusTerm -> Doc ann
    prettyAtomic = \case
        v@Var{} -> prettyNoBind v
        c@Constant{} -> prettyNoBind c
        e@Error{} -> prettyNoBind e
        d@Delay{} -> prettyNoBind d
        f@Force{} -> prettyNoBind f
        b@Builtin{} -> prettyNoBind b
        other -> align . group . parens . prettyNoBind $ other
    analyzeApp :: PlutusTerm -> [PlutusTerm]
    analyzeApp = \case
        Apply () f arg -> analyzeApp f <> [arg]
        other -> [other]
pConstant :: AConstant -> PlutusTerm
pConstant = \case
    AUnit -> mkConstant () ()
    ABoolean b -> mkConstant () b
    AnInteger i -> mkConstant () i
    AByteString bs -> mkConstant () bs
    AString txt -> mkConstant () txt

-- | Makes the SOP Constr
pConstr :: Word64 -> Vector PlutusTerm -> PlutusTerm
pConstr w = Constr () w . Vector.toList

plutus_I :: Integer -> PlutusTerm
plutus_I i = pBuiltin IData # mkConstant () i

-- Makes a Constr PlutusData
plutus_ConstrData :: Integer -> Vector PlutusTerm -> PlutusTerm
plutus_ConstrData cix ctorArgs = constrData (mkConstant () cix) (pBuiltinList pNilData ctorArgs)

-- these _Data functions probably correspond to builtins, I'll look up their names later
-- NOTE: I guess we could do these in the ASG by applying a builtin function.
--       That might be easier than doing it in Plutus. Not sure.
-- 'I'
iData :: PlutusTerm -> PlutusTerm
iData t = pBuiltin IData # t

unIData :: PlutusTerm -> PlutusTerm
unIData t = pBuiltin UnIData # t

-- 'B'
bData :: PlutusTerm -> PlutusTerm
bData t = pBuiltin BData # t

-- 'Constr' (The data one)

{- | This exepects a non-data-encoded Integer term for the first arg.
TODO Check that that's what we give it anywhere it might be used
-}
constrData :: PlutusTerm -> PlutusTerm -> PlutusTerm
constrData cix ctorArgs = pBuiltin ConstrData # cix # ctorArgs

-- This rips apart a (data) Constr and returns the (Int,[Data]) pair (at the PLC level)
unConstrData :: PlutusTerm -> PlutusTerm
unConstrData t = pBuiltin UnConstrData # t

-- does not apply anything to the handlers
caseConstrEnum :: PlutusTerm -> Vector PlutusTerm -> PlutusTerm
caseConstrEnum scrut handlers = pCase ctorIx handlers
  where
    ctorIx = pFst (unConstrData scrut)

-- convenience for pApp FstPair
pFst :: PlutusTerm -> PlutusTerm
pFst aPair = pBuiltin FstPair # aPair

-- convenicne for pApp SndPair
pSnd :: PlutusTerm -> PlutusTerm
pSnd aPair = pBuiltin SndPair # aPair

pCons :: PlutusTerm -> PlutusTerm -> PlutusTerm
pCons x xs = pBuiltin MkCons # x # xs

pNilData :: PlutusTerm
pNilData = Constant () $ someValue @[Data] []

-- | Uses `case` and not `IfThenElse`
pIf :: PlutusTerm -> PlutusTerm -> PlutusTerm -> PlutusTerm
pIf cond t f = pCase cond [f, t]

(#-) :: PlutusTerm -> PlutusTerm -> PlutusTerm
x #- y =
    let minus = Builtin () PB.SubtractInteger
     in minus # x # y

(#<=) :: PlutusTerm -> PlutusTerm -> PlutusTerm
x #<= y =
    let lte = Builtin () PB.LessThanEqualsInteger
     in lte # x # y

(#<) :: PlutusTerm -> PlutusTerm -> PlutusTerm
x #< y = pBuiltin LessThanInteger # x # y

(#==) :: PlutusTerm -> PlutusTerm -> PlutusTerm
x #== y = pBuiltin EqualsInteger # x # y

(#+) :: PlutusTerm -> PlutusTerm -> PlutusTerm
x #+ y = pBuiltin AddInteger # x # y

(#!) :: PlutusTerm -> PlutusTerm -> PlutusTerm
bs #! ix = pBuiltin IndexByteString # bs # ix

-- This makes a builtin list, not data-wrapped
pBuiltinList :: PlutusTerm -> Vector PlutusTerm -> PlutusTerm
pBuiltinList nil = Vector.foldr pCons nil

-- This makes the PLUTUS DATA LIST (not a builtin list)
listData :: Vector PlutusTerm -> PlutusTerm
listData els = pBuiltin ListData # pBuiltinList pNilData els

-- List xs -> xs
unListData :: PlutusTerm -> PlutusTerm
unListData t = pBuiltin UnListData # t

pHead :: PlutusTerm -> PlutusTerm
pHead t = pBuiltin HeadList # t

pTail :: PlutusTerm -> PlutusTerm
pTail t = pBuiltin TailList # t

mapData :: Vector PlutusTerm -> PlutusTerm
mapData t = pBuiltin MapData # pBuiltinList pNilData t

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
pBuiltin :: forall t. (IsBuiltin t) => t -> PlutusTerm
pBuiltin = pMkBuiltin . mkBuiltin

data SomeBuiltin where
    SomeBuiltin1 :: OneArgFunc -> SomeBuiltin
    SomeBuiltin2 :: TwoArgFunc -> SomeBuiltin
    SomeBuiltin3 :: ThreeArgFunc -> SomeBuiltin
    SomeBuiltin6 :: SixArgFunc -> SomeBuiltin

pMkBuiltin :: SomeBuiltin -> PlutusTerm
pMkBuiltin = \case
    SomeBuiltin1 bi -> case bi of
        LengthOfByteString -> Builtin () PB.LengthOfByteString
        Sha2_256 -> Builtin () PB.Sha2_256
        Sha3_256 -> Builtin () PB.Sha3_256
        Blake2b_256 -> Builtin () PB.Blake2b_256
        EncodeUtf8 -> Builtin () PB.EncodeUtf8
        DecodeUtf8 -> Builtin () PB.DecodeUtf8
        FstPair -> pForce $ pForce $ Builtin () PB.FstPair
        SndPair -> pForce $ pForce $ Builtin () PB.SndPair
        HeadList -> pForce $ Builtin () PB.HeadList
        TailList -> pForce $ Builtin () PB.TailList
        NullList -> pForce $ Builtin () PB.NullList
        MapData -> Builtin () PB.MapData
        ListData -> Builtin () PB.ListData
        IData -> Builtin () PB.IData
        BData -> Builtin () PB.BData
        UnConstrData -> Builtin () PB.UnConstrData
        UnMapData -> Builtin () PB.UnMapData
        UnListData -> Builtin () PB.UnListData
        UnIData -> Builtin () PB.UnIData
        UnBData -> Builtin () PB.UnBData
        SerialiseData -> Builtin () PB.SerialiseData
        BLS12_381_G1_neg -> Builtin () PB.Bls12_381_G1_neg
        BLS12_381_G1_compress -> Builtin () PB.Bls12_381_G1_compress
        BLS12_381_G1_uncompress -> Builtin () PB.Bls12_381_G1_uncompress
        BLS12_381_G2_neg -> Builtin () PB.Bls12_381_G2_neg
        BLS12_381_G2_compress -> Builtin () PB.Bls12_381_G2_compress
        BLS12_381_G2_uncompress -> Builtin () PB.Bls12_381_G2_uncompress
        Keccak_256 -> Builtin () PB.Keccak_256
        Blake2b_224 -> Builtin () PB.Blake2b_224
        ComplementByteString -> Builtin () PB.ComplementByteString
        CountSetBits -> Builtin () PB.CountSetBits
        FindFirstSetBit -> Builtin () PB.FindFirstSetBit
        Ripemd_160 -> Builtin () PB.Ripemd_160
    SomeBuiltin2 bi -> case bi of
        AddInteger -> Builtin () PB.AddInteger
        SubtractInteger -> Builtin () PB.SubtractInteger
        MultiplyInteger -> Builtin () PB.MultiplyInteger
        DivideInteger -> Builtin () PB.DivideInteger
        QuotientInteger -> Builtin () PB.QuotientInteger
        RemainderInteger -> Builtin () PB.RemainderInteger
        ModInteger -> Builtin () PB.ModInteger
        EqualsInteger -> Builtin () PB.EqualsInteger
        LessThanInteger -> Builtin () PB.LessThanInteger
        LessThanEqualsInteger -> Builtin () PB.LessThanEqualsInteger
        AppendByteString -> Builtin () PB.AppendByteString
        ConsByteString -> Builtin () PB.ConsByteString
        IndexByteString -> Builtin () PB.IndexByteString
        EqualsByteString -> Builtin () PB.EqualsByteString
        LessThanByteString -> Builtin () PB.LessThanByteString
        LessThanEqualsByteString -> Builtin () PB.LessThanEqualsByteString
        AppendString -> Builtin () PB.AppendString
        EqualsString -> Builtin () PB.EqualsString
        ChooseUnit -> pForce $ Builtin () PB.ChooseUnit
        Trace -> pForce $ Builtin () PB.Trace
        MkCons -> pForce $ Builtin () PB.MkCons
        ConstrData -> Builtin () PB.ConstrData
        EqualsData -> Builtin () PB.EqualsData
        MkPairData -> Builtin () PB.MkPairData
        BLS12_381_G1_add -> Builtin () PB.Bls12_381_G1_add
        BLS12_381_G1_scalarMul -> Builtin () PB.Bls12_381_G1_scalarMul
        BLS12_381_G1_equal -> Builtin () PB.Bls12_381_G1_equal
        BLS12_381_G1_hashToGroup -> Builtin () PB.Bls12_381_G1_hashToGroup
        BLS12_381_G2_add -> Builtin () PB.Bls12_381_G2_add
        BLS12_381_G2_scalarMul -> Builtin () PB.Bls12_381_G2_scalarMul
        BLS12_381_G2_equal -> Builtin () PB.Bls12_381_G2_equal
        BLS12_381_G2_hashToGroup -> Builtin () PB.Bls12_381_G2_hashToGroup
        BLS12_381_millerLoop -> Builtin () PB.Bls12_381_millerLoop
        BLS12_381_mulMlResult -> Builtin () PB.Bls12_381_mulMlResult
        BLS12_381_finalVerify -> Builtin () PB.Bls12_381_finalVerify
        ByteStringToInteger -> Builtin () PB.ByteStringToInteger
        ReadBit -> Builtin () PB.ReadBit
        ReplicateByte -> Builtin () PB.ReplicateByte
        ShiftByteString -> Builtin () PB.ShiftByteString
        RotateByteString -> Builtin () PB.RotateByteString
    SomeBuiltin3 bi -> case bi of
        VerifyEd25519Signature -> Builtin () PB.VerifyEd25519Signature
        VerifyEcdsaSecp256k1Signature -> Builtin () PB.VerifyEcdsaSecp256k1Signature
        VerifySchnorrSecp256k1Signature -> Builtin () PB.VerifySchnorrSecp256k1Signature
        IfThenElse -> pForce $ Builtin () PB.IfThenElse
        ChooseList -> pForce $ Builtin () PB.ChooseList
        IntegerToByteString -> Builtin () PB.IntegerToByteString
        AndByteString -> Builtin () PB.AndByteString
        OrByteString -> Builtin () PB.OrByteString
        XorByteString -> Builtin () PB.XorByteString
        WriteBits -> Builtin () PB.WriteBits
        ExpModInteger -> Builtin () PB.ExpModInteger
    SomeBuiltin6 bi6 -> case bi6 of
        ChooseData -> pForce $ Builtin () PB.ChooseData

mkBuiltinCase :: forall a. (Show a) => Int -> String -> [a] -> String
mkBuiltinCase indent var ctors = "case " <> var <> " of" <> cases
  where
    cases = foldl' go "" ctors
    go :: String -> a -> String
    go acc (show -> ctor) = acc <> "\n" <> replicate indent ' ' <> ctor <> " -> " <> "Builtin () PB." <> ctor

oneArgFuncs :: [OneArgFunc]
oneArgFuncs =
    [ LengthOfByteString
    , Sha2_256
    , Sha3_256
    , Blake2b_256
    , EncodeUtf8
    , DecodeUtf8
    , FstPair
    , SndPair
    , HeadList
    , TailList
    , NullList
    , MapData
    , ListData
    , IData
    , BData
    , UnConstrData
    , UnMapData
    , UnListData
    , UnIData
    , UnBData
    , SerialiseData
    , BLS12_381_G1_neg
    , BLS12_381_G1_compress
    , BLS12_381_G1_uncompress
    , BLS12_381_G2_neg
    , BLS12_381_G2_compress
    , BLS12_381_G2_uncompress
    , Keccak_256
    , Blake2b_224
    , ComplementByteString
    , CountSetBits
    , FindFirstSetBit
    , Ripemd_160
    ]

twoArgFuncs :: [TwoArgFunc]
twoArgFuncs =
    [ AddInteger
    , SubtractInteger
    , MultiplyInteger
    , DivideInteger
    , QuotientInteger
    , RemainderInteger
    , ModInteger
    , EqualsInteger
    , LessThanInteger
    , LessThanEqualsInteger
    , AppendByteString
    , ConsByteString
    , IndexByteString
    , EqualsByteString
    , LessThanByteString
    , LessThanEqualsByteString
    , AppendString
    , EqualsString
    , ChooseUnit
    , Trace
    , MkCons
    , ConstrData
    , EqualsData
    , MkPairData
    , BLS12_381_G1_add
    , BLS12_381_G1_scalarMul
    , BLS12_381_G1_equal
    , BLS12_381_G1_hashToGroup
    , BLS12_381_G2_add
    , BLS12_381_G2_scalarMul
    , BLS12_381_G2_equal
    , BLS12_381_G2_hashToGroup
    , BLS12_381_millerLoop
    , BLS12_381_mulMlResult
    , BLS12_381_finalVerify
    , ByteStringToInteger
    , ReadBit
    , ReplicateByte
    , ShiftByteString
    , RotateByteString
    ]

threeArgFuncs :: [ThreeArgFunc]
threeArgFuncs =
    [ VerifyEd25519Signature
    , VerifyEcdsaSecp256k1Signature
    , VerifySchnorrSecp256k1Signature
    , IfThenElse
    , ChooseList
    , IntegerToByteString
    , AndByteString
    , OrByteString
    , XorByteString
    , WriteBits
    , ExpModInteger
    ]

sixArgFuncs :: [SixArgFunc]
sixArgFuncs = [ChooseData]
