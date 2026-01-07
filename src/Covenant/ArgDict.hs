{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Use <$>" -}
-- Seriously WTF this makes things so much uglier!
module Covenant.ArgDict (preprocess) where

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
import Covenant.Type (AbstractTy (BoundAt), CompT (CompN), CompTBody (ArgsAndResult))

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.ExtendedASG
import Covenant.Index (Index, intCount, intIndex)
import Covenant.Test (Id (UnsafeMkId))
import Covenant.Transform.Pipeline.Common ()
import Covenant.Transform.TyUtils
import Data.Maybe (fromJust)
import Optics.Core (preview, review)
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

preprocess :: ExtendedASG -> Map Id (Either (Vector Name) (Vector Id))
preprocess asg = fst $ evalRWS go mempty asg
  where
    go :: RWS (Vector Id) () ExtendedASG (Map Id (Either (Vector Name) (Vector Id)))
    go = do
        topId <- fst <$> eTopLevelSrcNode
        mkArgResolutionDict (forgetExtendedId topId)

mkArgResolutionDict ::
    Id -> -- needs to be the source node for top level calls of this fn
    RWS (Vector Id) () ExtendedASG (Map Id (Either (Vector Name) (Vector Id)))
mkArgResolutionDict i =
    eNodeAt i >>= \case
        AnError -> notALambda $ pure M.empty
        ACompNode compT compNode -> case compNode of
            Lam bodyRef -> do
                let numVarsBoundHere = compTArgs compT
                    idW = idToWord i
                names <- Vector.fromList <$> traverse (lamArgName idW) [0 .. numVarsBoundHere]
                case bodyRef of
                    AnId child -> local (Vector.cons i) $ do
                        res <- mkArgResolutionDict child
                        pure $ safeInsert i (Left names) res
                    AnArg _ -> pure $ M.singleton i (Left names)
            Force fRef -> notALambda $ goRef fRef
            _someBuiltin -> notALambda $ pure M.empty
        AValNode _valT valNode -> case valNode of
            Lit _ -> notALambda $ pure M.empty
            App fn args _ _ -> notALambda $ do
                fnDict <- mkArgResolutionDict fn
                argsDicts <- mconcat <$> traverse goRef (Vector.toList args)
                pure $ fnDict <> argsDicts
            Thunk child -> notALambda $ mkArgResolutionDict child
            Cata ty handlers arg -> notALambda $ mconcat <$> traverse goRef (arg : Vector.toList handlers)
            DataConstructor _tn _cn args -> notALambda $ mconcat <$> traverse goRef (Vector.toList args)
            Match scrut handlers -> notALambda $ mconcat <$> traverse goRef (scrut : Vector.toList handlers)
  where
    safeInsert :: forall (k :: Type) (v :: Type). (Ord k) => k -> v -> Map k v -> Map k v
    safeInsert k v = M.alter (\case Nothing -> Just v; other -> other) k

    lamArgName :: Word64 -> Int -> RWS (Vector Id) () ExtendedASG Name
    lamArgName i' argPos = do
        let txtPart = "arg_" <> T.pack (show i') <> "_" <> T.pack (show argPos)
        (UnsafeMkId uniqueW) <- nextId
        pure $ Name txtPart (Unique (fromIntegral uniqueW))

    goRef :: Ref -> RWS (Vector Id) () ExtendedASG (Map Id (Either (Vector Name) (Vector Id)))
    goRef = \case
        AnArg _ -> pure M.empty
        AnId anId -> mkArgResolutionDict anId

    notALambda ::
        RWS (Vector Id) () ExtendedASG (Map Id (Either (Vector Name) (Vector Id))) ->
        RWS (Vector Id) () ExtendedASG (Map Id (Either (Vector Name) (Vector Id)))
    notALambda act = do
        here <- Right <$> ask
        there <- act
        pure . safeInsert i here $ there
