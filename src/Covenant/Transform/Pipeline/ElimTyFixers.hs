{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.ElimTyFixers
  ( transformTypeFixerNodes,
  )
where

import Control.Monad.RWS.Strict (MonadReader (ask))
import Control.Monad.State.Strict (MonadState, gets, modify')
import Covenant.ASG
  ( ASGNode (ACompNode, AValNode, AnError),
    ASGNodeType (ValNodeType),
    CompNodeInfo (Force, Lam),
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    typeASGNode,
  )
import Covenant.CodeGen.Stubs (MonadStub, stubId)
import Covenant.ExtendedASG
  ( ExtendedId,
    eInsert,
    eNodeAt,
    eTopLevelSrcNode,
    forgetExtendedId,
    resolveExtended,
    tyFixerFnId,
  )
import Covenant.Test (Arg (UnsafeMkArg), ValNodeInfo (AppInternal))
import Covenant.Transform.Common
  ( cataData,
    introData,
    matchData,
    tyFixerFnTy,
  )
import Covenant.Transform.Pipeline.Common
  ( TransformState,
    UniqueError (UniqueError),
    mapField,
    syntheticLamNode,
  )
import Covenant.Transform.Pipeline.Monad (Datatypes (Datatypes))
import Covenant.Transform.TyUtils (applyArgs)
import Covenant.Type
  ( AbstractTy,
    CompT (CompN),
    CompTBody (ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    PlutusDataConstructor
      ( PlutusB,
        PlutusConstr,
        PlutusI,
        PlutusList,
        PlutusMap
      ),
    TyName,
    ValT (Datatype),
  )
import Data.Foldable
  ( traverse_,
  )
import Data.Kind (Type)
import Data.Map qualified as M
import Data.Row.Records (Rec)
import Data.Row.Records qualified as R
import Data.Set qualified as S
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Optics.Core (view)

{- Rewrites type fixer nodes into applications.

   This also constructs and inserts dummy functions into the ASG
-}
transformTypeFixerNodes ::
  forall (m :: Type -> Type).
  ( MonadStub m,
    MonadState (Rec TransformState) m,
    MonadReader Datatypes m
  ) =>
  m ()
transformTypeFixerNodes = do
  topSrcNode <- fst <$> eTopLevelSrcNode
  go topSrcNode --  dtDict magicErr tyFixers
  where
    conjureFunction :: CompT AbstractTy -> m ASGNode
    conjureFunction compT = do
      errId <- stubId "error"
      pure $ syntheticLamNode (UniqueError errId) compT

    resolveCtorIx :: TyName -> ConstructorName -> m (Maybe Int)
    resolveCtorIx tn cn = do
      dtInfo <- (\(Datatypes x) -> x M.! tn) <$> ask
      case view #originalDecl dtInfo of
        OpaqueData _ ctors -> do
          -- TODO/REVIEW: NEED TO CHECK THAT THIS NAMING IS CONSISTENT WITH ANYWHERE ELSE WE HANDLE THIS
          let (ConstructorName inner) = cn
              mplutusDataCtor = case inner of
                "I" -> Just PlutusI
                "B" -> Just PlutusB
                "Constr" -> Just PlutusConstr
                "List" -> Just PlutusList
                "Map" -> Just PlutusMap
                _ -> Nothing
          case mplutusDataCtor of
            Nothing -> pure Nothing
            Just plutusDataCtor ->
              pure $ Vector.findIndex (== plutusDataCtor) (Vector.fromList . Set.toList $ ctors)
        DataDeclaration _ _ ctors _ -> pure $ Vector.findIndex (\(Constructor cNm' _) -> cNm' == cn) ctors

    -- this should only be used in contexts where we must have a datatype (e.g. scrutinees in matches and catas, parts of generated functions)
    unsafeDatatypeName :: ValT AbstractTy -> TyName
    unsafeDatatypeName = \case
      Datatype tn _ -> tn
      other -> error $ "unsafeDatatypeName called on non-datatype ValT: " <> show other

    -- only use this on things that have to be a value type (i.e. scrutinees)
    unsafeRefType :: Ref -> m (ValT AbstractTy)
    unsafeRefType = \case
      AnArg (UnsafeMkArg _ _ ty) -> pure ty
      AnId i ->
        eNodeAt i >>= \node -> case typeASGNode node of
          ValNodeType ty -> pure ty
          other -> error $ "UnsafeRefType called on an Id with a non-ValT type: " <> show other

    alreadyVisited :: ExtendedId -> m Bool
    alreadyVisited i = S.member i <$> gets (R..! #visited)

    insertAndMarkVisited :: ExtendedId -> ASGNode -> m ()
    insertAndMarkVisited eid node = do
      eInsert eid node
      oldVisited <- gets (R..! #visited)
      modify' $ R.update #visited (S.insert eid oldVisited)

    go :: ExtendedId -> m ()
    go i =
      alreadyVisited i >>= \case
        True -> pure ()
        False ->
          eNodeAt i >>= \case
            AnError -> pure ()
            ACompNode _compT compNode -> case compNode of
              Lam ref -> goRef ref
              Force ref -> goRef ref
              _ -> pure ()
            AValNode valT valNode -> case valNode of
              Lit _ -> pure ()
              Thunk child -> resolveExtended child >>= go
              App fn args _ _ -> do
                resolveExtended fn >>= go
                traverse_ goRef args
              Cata cataT handlers arg -> do
                tyFixers <- gets (R..! #tyFixerData)
                tn <- unsafeDatatypeName <$> unsafeRefType arg
                let getTyFixer = case M.lookup tn tyFixers of
                      Just bundle -> Just bundle
                      Nothing -> case cataT of
                        (CompN _ (Datatype bfTn _ :--:> ReturnT _)) -> M.lookup bfTn tyFixers
                        _ -> Nothing
                case cataData =<< getTyFixer of
                  Nothing -> error $ "Fatal Error: No type fixer function data for catamorphisms on " <> show tn
                  Just dat -> do
                    let cataFnPolyTy = tyFixerFnTy dat
                    cataId <- tyFixerFnId
                    modify' $ mapField #tyFixers (M.insert (forgetExtendedId cataId) dat)
                    handlerTypes <- traverse unsafeRefType (Vector.toList handlers)
                    scrutTy <- unsafeRefType arg
                    let cataFnConcrete = applyArgs cataFnPolyTy (scrutTy : handlerTypes)
                        -- DOUBLE CHECK WHETHER `i` is the right ID here TODO/FIXME/REVIEW
                        newValNode = AppInternal (forgetExtendedId cataId) (Vector.cons arg handlers) Vector.empty cataFnConcrete
                        newASGNode = AValNode valT newValNode
                    insertAndMarkVisited i newASGNode
                    -- NOTE: This is just a placeholder tagged with the polymorphic function type, which we need.
                    --       The body is a reference to a single error node that we track and will ignore/remove.
                    --       TODO: There's only one of these for each type so add a check to save us work if we already did it
                    syntheticCataFnNode <- conjureFunction cataFnPolyTy
                    insertAndMarkVisited cataId syntheticCataFnNode
                traverse_ goRef handlers
                goRef arg
              Match scrut handlers -> do
                matchId <- tyFixerFnId
                scrutTy <- unsafeRefType scrut
                handlerTypes <- traverse unsafeRefType $ Vector.toList handlers
                let tn = unsafeDatatypeName scrutTy
                tyFixers <- gets (R..! #tyFixerData)
                case matchData =<< M.lookup tn tyFixers of
                  Nothing ->
                    error $
                      "Fatal Error: No type fixer function data for pattern matches on " <> show tn
                  Just dat -> do
                    let matchFnPolyTy = tyFixerFnTy dat
                    modify' $ mapField #tyFixers (M.insert (forgetExtendedId matchId) dat)
                    let matchFnConcrete = applyArgs matchFnPolyTy (scrutTy : handlerTypes)
                        newValNode = AppInternal (forgetExtendedId matchId) (Vector.cons scrut handlers) Vector.empty matchFnConcrete
                        newASGNode = AValNode valT newValNode
                    insertAndMarkVisited i newASGNode
                    -- NOTE: See previous note
                    syntheticMatchFnNode <- conjureFunction matchFnPolyTy
                    insertAndMarkVisited matchId syntheticMatchFnNode
                traverse_ goRef handlers
                goRef scrut
              DataConstructor tn ctorName ctorArgs -> do
                argTys <- traverse unsafeRefType $ Vector.toList ctorArgs
                tyFixers <- gets (R..! #tyFixerData)
                case introData <$> M.lookup tn tyFixers of
                  Nothing ->
                    error $
                      "Fatal Error: No type fixer function data for datatype introductions for type " <> show tn
                  Just constrFunctions ->
                    resolveCtorIx tn ctorName >>= \case
                      Nothing -> error $ "Fatal Error: No data for constructor " <> show ctorName <> " found in type " <> show tn
                      Just ctorIx -> do
                        ctorFnId <- tyFixerFnId
                        let dat = constrFunctions Vector.! ctorIx
                            ctorFnPolyTy = tyFixerFnTy dat
                            ctorFnConcrete = applyArgs ctorFnPolyTy argTys
                            newValNode = AppInternal (forgetExtendedId ctorFnId) ctorArgs Vector.empty ctorFnConcrete
                            newASGNode = AValNode valT newValNode
                        modify' $ mapField #tyFixers (M.insert (forgetExtendedId ctorFnId) dat)
                        insertAndMarkVisited i newASGNode
                        -- NOTE: See previous note
                        syntheticCtorFnNode <- conjureFunction ctorFnPolyTy
                        insertAndMarkVisited ctorFnId syntheticCtorFnNode
                traverse_ goRef ctorArgs
      where
        goRef :: Ref -> m ()
        goRef = \case
          AnId child -> resolveExtended child >>= go
          AnArg {} -> pure ()
