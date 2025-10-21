{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Use <$>" -}
-- Seriously WTF this makes things so much uglier!
module Covenant.ArgDict (preprocess, idToName) where

import Data.Word (Word64)

import Data.Kind (Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Text qualified as T

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, evalRWS, get, local, modify)

import Covenant.ASG (
    ASG,
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId,
 )
import Covenant.Type (AbstractTy, CompT (CompN), CompTBody (ArgsAndResult))

import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

preprocess :: ASG -> Map Id (Either (Vector Name) (Vector Id))
preprocess asg = fst $ evalRWS (mkArgResolutionDict asg (topLevelId asg)) mempty (succ . fromEnum . topLevelId $ asg)

mkArgResolutionDict ::
    ASG ->
    Id -> -- needs to be the source node for top level calls of this fn
    RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id)))
mkArgResolutionDict asg i = case nodeAt i asg of
    AnError -> notALambda $ pure M.empty
    ACompNode compT compNode -> case compNode of
        Lam bodyRef -> do
            let numVarsBoundHere = compTArgs compT
                idW = idToWord i
            names <- Vector.fromList <$> traverse (lamArgName idW) [0 .. numVarsBoundHere]
            case bodyRef of
                AnId child -> local (Vector.cons i) $ do
                    res <- mkArgResolutionDict asg child
                    pure $ safeInsert i (Left names) res
                AnArg _ -> pure $ M.singleton i (Left names)
        Force fRef -> notALambda $ goRef fRef
        _someBuiltin -> notALambda $ pure M.empty
    AValNode _valT valNode -> case valNode of
        Lit _ -> notALambda $ pure M.empty
        App fn args _ -> notALambda $ do
            fnDict <- mkArgResolutionDict asg fn
            argsDicts <- mconcat <$> traverse goRef (Vector.toList args)
            pure $ fnDict <> argsDicts
        Thunk child -> notALambda $ mkArgResolutionDict asg child
        Cata alg arg -> notALambda $ (<>) <$> goRef alg <*> goRef arg
        DataConstructor _tn _cn args -> notALambda $ mconcat <$> traverse goRef (Vector.toList args)
        Match scrut handlers -> notALambda $ mconcat <$> traverse goRef (scrut : Vector.toList handlers)
  where
    safeInsert :: forall (k :: Type) (v :: Type). (Ord k) => k -> v -> Map k v -> Map k v
    safeInsert k v = M.alter (\case Nothing -> Just v; other -> other) k

    lamArgName :: Word64 -> Int -> RWS (Vector Id) () Int Name
    lamArgName i' argPos = do
        let txtPart = "arg_" <> T.pack (show i') <> "_" <> T.pack (show argPos)
        uniquePart <- nextArgUnique
        pure $ Name txtPart (Unique uniquePart)

    nextArgUnique :: RWS (Vector Id) () Int Int
    nextArgUnique = do
        n <- get
        modify (+ 1)
        pure n

    goRef :: Ref -> RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id)))
    goRef = \case
        AnArg _ -> pure M.empty
        AnId anId -> mkArgResolutionDict asg anId

    notALambda ::
        RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id))) ->
        RWS (Vector Id) () Int (Map Id (Either (Vector Name) (Vector Id)))
    notALambda act = do
        here <- Right <$> ask
        there <- act
        pure . safeInsert i here $ there

compTArgs :: CompT AbstractTy -> Int
compTArgs = \case
    CompN _ (ArgsAndResult args _) -> Vector.length args - 1

-- We really should have a better way of doing this.
idToWord :: Id -> Word64
idToWord = toEnum . fromEnum

idToName :: Id -> Name
idToName i = Name ("x_" <> T.pack (show $ fromEnum i)) (Unique (fromEnum i))
