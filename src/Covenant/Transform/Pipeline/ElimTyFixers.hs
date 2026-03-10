{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
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
import Covenant.Data (mapValT)
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.ExtendedASG
  ( ExtendedId (TyFixerFn, WrappedSrc),
    MonadASG (getASG),
    eInsert,
    eNodeAt,
    eTopLevelSrcNode,
    forgetExtendedId,
    nextId,
    resolveExtended,
    tyFixerFnId,
    unExtendedASG,
  )
import Covenant.Index (ix0)
import Covenant.Prim (OneArgFunc (BData, IData, ListData, MapData), TwoArgFunc (ConstrData))
import Covenant.Transform.Common ()
import Covenant.Transform.Pipeline.Common
  ( TransformState,
    UniqueError (UniqueError),
    lookupDatatypeInfo,
    mapField,
    syntheticLamNode,
  )
import Covenant.Transform.Pipeline.Monad (Datatypes (Datatypes))
import Covenant.Transform.TyUtils (applyArgs, substCompT)
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (Comp0, Comp1, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
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
    ValT (Abstraction, Datatype, ThunkT),
    byteStringT,
    integerT,
    tyvar,
  )
import Covenant.Unsafe (Arg (UnsafeMkArg), CompNodeInfo (Builtin1Internal, Builtin2Internal), Id, ValNodeInfo (AppInternal))
import Data.Foldable
  ( traverse_,
  )
import Data.Kind (Type)
import Data.List (find)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.Row.Records (Rec)
import Data.Row.Records qualified as R
import Data.Set (Set)
import Data.Set qualified as S
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Vector qualified as Vector
import Debug.Trace (traceM)
import Optics.Core (view)

{- Rewrites type fixer nodes into applications.

   This also constructs and inserts dummy functions into the ASG
-}
transformTypeFixerNodes ::
  forall (m :: Type -> Type).
  ( MonadStub m
  , MonadState (Rec TransformState) m
  , MonadReader Datatypes m
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
                case view #cataData =<< getTyFixer of
                  Nothing -> error $ "Fatal Error: No type fixer function data for catamorphisms on " <> show tn
                  Just dat -> do
                    let cataFnPolyTy = view #fnTy dat
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
                traceM "match"
                lookupOpaqueRef scrut >>= \case
                  Just opaqueCtors -> do
                    traceM "match.opaque"
                    handlersWithErrors <- mkOpaqueHandlers opaqueCtors handlers
                    -- we need to make a node for the "match on opaque" function. This is really just
                    -- the match function for Data, but we have to handle it differently for implementation reasons
                    syntheticMatchFnNode <- conjureFunction matchOpaquePolyTy
                    let subs = M.singleton (BoundAt Z ix0) valT -- WE MIGHT HAVE TO INC THE DB IN THE RES TY BY 1, I'm not sure
                        opaqueMatchFnConcrete = substCompT id subs matchOpaquePolyTy
                    matchDataId <- stubId "matchData"
                    insertAndMarkVisited (TyFixerFn matchDataId) syntheticMatchFnNode
                    let newValNode = AppInternal matchDataId (Vector.cons scrut handlersWithErrors) Vector.empty opaqueMatchFnConcrete
                        newASGNode = AValNode valT newValNode
                    insertAndMarkVisited i newASGNode
                  Nothing -> do
                    traceM "match.non-opaque"
                    matchId <- tyFixerFnId
                    scrutTy <- unsafeRefType scrut
                    handlerTypes <- traverse unsafeRefType $ Vector.toList handlers
                    let tn = unsafeDatatypeName scrutTy
                    tyFixers <- gets (R..! #tyFixerData)
                    case view #matchData =<< M.lookup tn tyFixers of
                      Nothing ->
                        error $
                          "Fatal Error: No type fixer function data for pattern matches on " <> show tn
                      Just dat -> do
                        let matchFnPolyTy = view #fnTy dat
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
              DataConstructor tn ctorName ctorArgs ->
                traceM "dataCon" >> lookupOpaque tn >>= \case
                  Just _cs -> do
                    traceM "datacon.opaque"
                    (opaqueIntroFnId, opaqueIntroFnTy) <- mkOpaqueIntroFn tn ctorName -- note: have this helper inject the a node into the ASG if needed
                    let newValNode = AppInternal opaqueIntroFnId ctorArgs Vector.empty opaqueIntroFnTy
                        newASGNode = AValNode valT newValNode
                    insertAndMarkVisited i newASGNode
                  Nothing -> do
                    traceM "datacon.non-opaque"
                    argTys <- traverse unsafeRefType $ Vector.toList ctorArgs
                    tyFixers <- gets (R..! #tyFixerData)
                    case view #introData <$> M.lookup tn tyFixers of
                      Nothing ->
                        error $
                          "Fatal Error: No type fixer function data for datatype introductions for type " <> show tn
                      Just constrFunctions ->
                        resolveCtorIx tn ctorName >>= \case
                          Nothing -> error $ "Fatal Error: No data for constructor " <> show ctorName <> " found in type " <> show tn
                          Just ctorIx -> do
                            ctorFnId <- tyFixerFnId
                            let dat = constrFunctions Vector.! ctorIx
                                ctorFnPolyTy = view #fnTy dat
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
          AnArg{} -> pure ()

        -- Stuff for opaques

        -- we don't have real hash consing anymore so we have to do something like this, which is annoying -_-
        findOrCreateNode :: (ASGNode -> Bool) -> (Id -> ExtendedId) -> ASGNode -> m Id
        findOrCreateNode p mkId node = do
          asg <- snd . unExtendedASG <$> getASG
          case find (p . snd) asg of
            Just (res, _) -> pure res
            Nothing -> do
              fresh <- nextId
              insertAndMarkVisited (mkId fresh) node
              pure fresh

        mkOpaqueIntroFn :: TyName -> ConstructorName -> m (Id, CompT AbstractTy)
        mkOpaqueIntroFn tn = \case
          "I" -> do
            let ty = tyHelper [integerT]
            fnId <- mkBuiltin1 IData ty
            pure (fnId, ty)
          "B" -> do
            let ty = tyHelper [byteStringT]
            fnId <- mkBuiltin1 BData ty
            pure (fnId, ty)
          "Constr" -> do
            let ty = tyHelper [integerT, listT dataT]
            fnId <- mkBuiltin2 ConstrData ty
            pure (fnId, ty)
          "Map" -> do
            let ty = tyHelper [listT (pairT dataT dataT)]
            fnId <- mkBuiltin1 MapData ty
            pure (fnId, ty)
          "List" -> do
            let ty = tyHelper [listT dataT]
            fnId <- mkBuiltin1 ListData ty
            pure (fnId, ty)
          ConstructorName other -> error $ T.unpack other <> " is not a valid Opaque constructor name!"
          where
            mkBuiltin1 :: OneArgFunc -> CompT AbstractTy -> m Id
            mkBuiltin1 fun1 funTy =
              findOrCreateNode
                (\case ACompNode _ (Builtin1Internal f) -> f == fun1; _ -> False)
                WrappedSrc -- I guess?
                (ACompNode funTy (Builtin1Internal fun1))

            mkBuiltin2 :: TwoArgFunc -> CompT AbstractTy -> m Id
            mkBuiltin2 fun2 funTy =
              findOrCreateNode
                (\case ACompNode _ (Builtin2Internal f) -> f == fun2; _ -> False)
                WrappedSrc -- I guess?
                (ACompNode funTy (Builtin2Internal fun2))

            tyHelper :: [ValT AbstractTy] -> CompT AbstractTy
            tyHelper args = Comp0 $ ArgsAndResult (Vector.fromList args) (Datatype tn [])

        lookupOpaqueRef :: Ref -> m (Maybe (Set PlutusDataConstructor))
        lookupOpaqueRef r = unsafeRefType r >>= lookupOpaqueType

        lookupOpaqueType :: ValT AbstractTy -> m (Maybe (Set PlutusDataConstructor))
        lookupOpaqueType = \case
          Datatype tn _ -> lookupOpaque tn
          _ -> pure Nothing

        lookupOpaque :: TyName -> m (Maybe (Set PlutusDataConstructor))
        lookupOpaque tn = do
          (view #originalDecl <$> lookupDatatypeInfo tn) >>= \case
            OpaqueData _ cs -> pure (Just cs)
            _ -> pure Nothing

        thunk0 :: forall (a :: Type). CompTBody a -> ValT a
        thunk0 = ThunkT . Comp0

        dataT :: ValT AbstractTy
        dataT = Datatype "Data" []

        listT :: ValT AbstractTy -> ValT AbstractTy
        listT t = Datatype "List" [t]

        a :: ValT AbstractTy
        a = tyvar Z ix0

        a' :: ValT AbstractTy
        a' = tyvar (S Z) ix0

        pairT :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
        pairT x y = Datatype "Pair" [x, y]

        _incDb :: ValT AbstractTy -> ValT AbstractTy
        _incDb =
          mapValT
            ( \case
                Abstraction (BoundAt db indx) -> Abstraction (BoundAt (S db) indx)
                other -> other
            )

        matchOpaquePolyTy :: CompT AbstractTy
        matchOpaquePolyTy =
          Comp1 $
            dataT
              :--:> thunk0 (integerT :--:> listT dataT :--:> ReturnT a')
              :--:> thunk0 (listT (pairT dataT dataT) :--:> ReturnT a')
              :--:> thunk0 (listT dataT :--:> ReturnT a')
              :--:> thunk0 (integerT :--:> ReturnT a')
              :--:> thunk0 (byteStringT :--:> ReturnT a')
              :--:> ReturnT a

        mkOpaqueHandlers :: Set PlutusDataConstructor -> Vector.Vector Ref -> m (Vector.Vector Ref)
        mkOpaqueHandlers opaqueCtors hs = do
          {- If our comments are to be believed, the canonical order for handlers should be:
                 [ PlutusI,
                   PlutusB,
                   PlutusConstr,
                   PlutusMap,
                   PlutusList
                ]

             So all we really need to do here is figure out which handlers we have, and fill the "gaps" with error nodes.

             Slight annoyance is that we have to persist the error nodes in the ASG, which we don't have to do for anything else here
             (for which an ephemeral error node that never gets generated will suffice).
          -}
          -- N.B. this is the order of the ord instance, it doesn't line up w/ what we need, this is faster than fixing it -_-
          let allCtors1 = [PlutusI, PlutusB, PlutusConstr, PlutusMap, PlutusList]
              orderedHandlers = goOrder M.empty opaqueCtors allCtors1 (Vector.toList hs)
              -- this is the order of the (non-scrutinee) arguments to matchData, which lines up neither with the ord instance nor the
              -- order we expect the handlers to be given in (...we should have made these things line up...)
              allCtors2 = Vector.fromList [PlutusConstr, PlutusMap, PlutusList, PlutusI, PlutusB]

          refToErrNode <- AnId <$> getErrNode
          let handlersWithErrs = fmap (\x -> fromMaybe refToErrNode (M.lookup x orderedHandlers)) allCtors2
          pure handlersWithErrs
          where
            goOrder :: Map PlutusDataConstructor Ref -> Set PlutusDataConstructor -> [PlutusDataConstructor] -> [Ref] -> Map PlutusDataConstructor Ref
            goOrder acc _ _ [] = acc
            goOrder acc _ [] _ = acc -- this can't happen
            goOrder acc thisTyCtors (maybeNextCtor : restCtors) (nextRef : restRefs)
              | maybeNextCtor `S.member` thisTyCtors = goOrder (M.insert maybeNextCtor nextRef acc) thisTyCtors restCtors restRefs
              | otherwise = goOrder acc thisTyCtors restCtors (nextRef : restRefs)

            -- this is inefficient but saves us from generating a large amount of error nodes we don't need if we already have one
            getErrNode :: m Id
            getErrNode = do
              asg <- snd . unExtendedASG <$> getASG
              case find (\x -> snd x == AnError) asg of
                Nothing -> do
                  -- we're just going to chuck it into the tree and pretend it's a normal source node
                  errI <- nextId
                  eInsert (WrappedSrc errI) AnError
                  pure errI
                Just (errI, _) -> pure errI
