module Covenant.CodeGen (
    oneArgFuncToPlutus,
    twoArgFuncToPlutus,
    threeArgFuncToPlutus,
    sixArgFuncToPlutus,
)
where

import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Prim qualified as CBuiltins
import PlutusCore.Default.Builtins (DefaultFun)
import PlutusCore.Default.Builtins qualified as PBuiltins

oneArgFuncToPlutus :: OneArgFunc -> DefaultFun
oneArgFuncToPlutus = \case
    CBuiltins.LengthOfByteString -> PBuiltins.LengthOfByteString
    CBuiltins.Sha2_256 -> PBuiltins.Sha2_256
    CBuiltins.Sha3_256 -> PBuiltins.Sha3_256
    CBuiltins.Blake2b_256 -> PBuiltins.Blake2b_256
    CBuiltins.EncodeUtf8 -> PBuiltins.EncodeUtf8
    CBuiltins.DecodeUtf8 -> PBuiltins.DecodeUtf8
    CBuiltins.FstPair -> PBuiltins.FstPair
    CBuiltins.SndPair -> PBuiltins.SndPair
    CBuiltins.HeadList -> PBuiltins.HeadList
    CBuiltins.TailList -> PBuiltins.TailList
    CBuiltins.NullList -> PBuiltins.NullList
    CBuiltins.MapData -> PBuiltins.MapData
    CBuiltins.ListData -> PBuiltins.ListData
    CBuiltins.IData -> PBuiltins.IData
    CBuiltins.BData -> PBuiltins.BData
    CBuiltins.UnConstrData -> PBuiltins.UnConstrData
    CBuiltins.UnMapData -> PBuiltins.UnMapData
    CBuiltins.UnListData -> PBuiltins.UnListData
    CBuiltins.UnIData -> PBuiltins.UnIData
    CBuiltins.UnBData -> PBuiltins.UnBData
    CBuiltins.SerialiseData -> PBuiltins.SerialiseData
    CBuiltins.BLS12_381_G1_neg -> PBuiltins.Bls12_381_G1_neg
    CBuiltins.BLS12_381_G1_compress -> PBuiltins.Bls12_381_G1_compress
    CBuiltins.BLS12_381_G1_uncompress -> PBuiltins.Bls12_381_G1_uncompress
    CBuiltins.BLS12_381_G2_neg -> PBuiltins.Bls12_381_G2_neg
    CBuiltins.BLS12_381_G2_compress -> PBuiltins.Bls12_381_G2_compress
    CBuiltins.BLS12_381_G2_uncompress -> PBuiltins.Bls12_381_G2_uncompress
    CBuiltins.Keccak_256 -> PBuiltins.Keccak_256
    CBuiltins.Blake2b_224 -> PBuiltins.Blake2b_224
    CBuiltins.ComplementByteString -> PBuiltins.ComplementByteString
    CBuiltins.CountSetBits -> PBuiltins.CountSetBits
    CBuiltins.FindFirstSetBit -> PBuiltins.FindFirstSetBit
    CBuiltins.Ripemd_160 -> PBuiltins.Ripemd_160

twoArgFuncToPlutus :: TwoArgFunc -> DefaultFun
twoArgFuncToPlutus = \case
    CBuiltins.AddInteger -> PBuiltins.AddInteger
    CBuiltins.SubtractInteger -> PBuiltins.SubtractInteger
    CBuiltins.MultiplyInteger -> PBuiltins.MultiplyInteger
    CBuiltins.DivideInteger -> PBuiltins.DivideInteger
    CBuiltins.QuotientInteger -> PBuiltins.QuotientInteger
    CBuiltins.RemainderInteger -> PBuiltins.RemainderInteger
    CBuiltins.ModInteger -> PBuiltins.ModInteger
    CBuiltins.EqualsInteger -> PBuiltins.EqualsInteger
    CBuiltins.LessThanInteger -> PBuiltins.LessThanInteger
    CBuiltins.LessThanEqualsInteger -> PBuiltins.LessThanEqualsInteger
    CBuiltins.AppendByteString -> PBuiltins.AppendByteString
    CBuiltins.ConsByteString -> PBuiltins.ConsByteString
    CBuiltins.IndexByteString -> PBuiltins.IndexByteString
    CBuiltins.EqualsByteString -> PBuiltins.EqualsByteString
    CBuiltins.LessThanByteString -> PBuiltins.LessThanByteString
    CBuiltins.LessThanEqualsByteString -> PBuiltins.LessThanEqualsByteString
    CBuiltins.AppendString -> PBuiltins.AppendString
    CBuiltins.EqualsString -> PBuiltins.EqualsString
    CBuiltins.ChooseUnit -> PBuiltins.ChooseUnit
    CBuiltins.Trace -> PBuiltins.Trace
    CBuiltins.MkCons -> PBuiltins.MkCons
    CBuiltins.ConstrData -> PBuiltins.ConstrData
    CBuiltins.EqualsData -> PBuiltins.EqualsData
    CBuiltins.MkPairData -> PBuiltins.MkPairData
    CBuiltins.BLS12_381_G1_add -> PBuiltins.Bls12_381_G1_add
    CBuiltins.BLS12_381_G1_equal -> PBuiltins.Bls12_381_G1_equal
    CBuiltins.BLS12_381_G1_hashToGroup -> PBuiltins.Bls12_381_G1_hashToGroup
    CBuiltins.BLS12_381_G1_scalarMul -> PBuiltins.Bls12_381_G1_scalarMul
    CBuiltins.BLS12_381_G2_add -> PBuiltins.Bls12_381_G2_add
    CBuiltins.BLS12_381_G2_equal -> PBuiltins.Bls12_381_G2_equal
    CBuiltins.BLS12_381_G2_hashToGroup -> PBuiltins.Bls12_381_G2_hashToGroup
    CBuiltins.BLS12_381_G2_scalarMul -> PBuiltins.Bls12_381_G2_scalarMul
    CBuiltins.BLS12_381_millerLoop -> PBuiltins.Bls12_381_millerLoop
    CBuiltins.BLS12_381_mulMlResult -> PBuiltins.Bls12_381_mulMlResult
    CBuiltins.BLS12_381_finalVerify -> PBuiltins.Bls12_381_finalVerify
    CBuiltins.ByteStringToInteger -> PBuiltins.ByteStringToInteger
    CBuiltins.ReadBit -> PBuiltins.ReadBit
    CBuiltins.ReplicateByte -> PBuiltins.ReplicateByte
    CBuiltins.ShiftByteString -> PBuiltins.ShiftByteString
    CBuiltins.RotateByteString -> PBuiltins.RotateByteString

threeArgFuncToPlutus :: ThreeArgFunc -> DefaultFun
threeArgFuncToPlutus = \case
    CBuiltins.VerifyEd25519Signature -> PBuiltins.VerifyEd25519Signature
    CBuiltins.VerifyEcdsaSecp256k1Signature -> PBuiltins.VerifyEcdsaSecp256k1Signature
    CBuiltins.VerifySchnorrSecp256k1Signature -> PBuiltins.VerifySchnorrSecp256k1Signature
    CBuiltins.IfThenElse -> PBuiltins.IfThenElse
    CBuiltins.ChooseList -> PBuiltins.ChooseList
    CBuiltins.IntegerToByteString -> PBuiltins.IntegerToByteString
    CBuiltins.AndByteString -> PBuiltins.AndByteString
    CBuiltins.OrByteString -> PBuiltins.OrByteString
    CBuiltins.XorByteString -> PBuiltins.XorByteString
    CBuiltins.WriteBits -> PBuiltins.WriteBits
    CBuiltins.ExpModInteger -> PBuiltins.ExpModInteger

sixArgFuncToPlutus :: SixArgFunc -> DefaultFun
sixArgFuncToPlutus = \case
    CBuiltins.ChooseData -> PBuiltins.ChooseData
