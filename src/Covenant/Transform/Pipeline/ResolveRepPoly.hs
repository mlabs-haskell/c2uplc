{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Pipeline.ResolveRepPoly where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set qualified as S
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, asks, local)

import Covenant.ASG (
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo (Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Thunk),
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    DataEncoding (SOP),
    ValT (Abstraction, BuiltinFlat, ThunkT),
 )

import Control.Monad (when, unless)
import Control.Monad.Reader (runReader)
import Covenant.DeBruijn (DeBruijn (Z), asInt)
import Covenant.Index (Index)
import Covenant.Test (ValNodeInfo (AppInternal))
import Data.Foldable (
    traverse_,
 )
import Data.Void (Void, vacuous)
import Optics.Core (review)


import Covenant.ExtendedASG
import Covenant.Transform.Common
import Data.Row.Records (Rec)
import Data.Row.Records qualified as R

import Covenant.Transform.Pipeline.Common
import Covenant.Transform.TyUtils 


{- By this point the entire asg is nothing but lam, app, thunk/force, and builtins/primitives

i need some kind of example

f :: Int -> Bool -> String -> ByteString
f i b s = (g i) (g b) (g (g s))
-}
resolveRepPoly :: RWS (Rec ConcretifyCxt) () ExtendedASG ()
resolveRepPoly = eTopLevelSrcNode >>= go . fst
  where
    traceError :: forall a. String -> RWS (Rec ConcretifyCxt) () ExtendedASG a
    traceError msg = do
      callPath <- asks (R..! #callPath)
      appPath <- asks (R..! #appPath)
      context <- asks (R..! #context)
      let errMsg =  "Encountered error while resolving representational polymorphism"
                    <> "\n  CallChain: " <> show callPath
                    <> "\n AppChain:" <> show appPath
                    <> "\n Context:" <> show context
                    <> "\n Error Message: " <> msg
                    <> "\n\n"
      error errMsg

    unsafeFnTy :: forall k. (ExtendedKey k) => k -> RWS (Rec ConcretifyCxt) () ExtendedASG (CompT AbstractTy)
    unsafeFnTy k = eNodeAt k >>= \case
      ACompNode compT _ -> pure compT
      other -> traceError $ "unsafeFnTy called on " <> show other <> " which isn't a comp node"

    goRef :: Ref -> RWS (Rec ConcretifyCxt) () ExtendedASG ()
    goRef = \case
      AnId i -> resolveExtended i >>= go
      AnArg{} -> pure ()

    dbBindingSite :: DeBruijn -> RWS (Rec ConcretifyCxt) () ExtendedASG LambdaId
    dbBindingSite db = do
      let dbInt = review asInt db
      scopeStack <- asks (R..! #callPath)
      pure $ scopeStack Vector.! dbInt

    {- This will be the thing that:
         1. Replaces the function type with one that has the handlers
         2. Applies the handlers
         3. Updates the type of the corresponding synthetic function (i.e. modifies the node) to
            explicitly mention the handlers (NOTE: THIS DOES NOT CONCRETIFY THE SYNTHETIC FUNCTION NODE)
    -}
    cleanupAppNode :: ExtendedId -> ASGNode  -> Map (Index "tyvar") (ValT Void) -> RWS (Rec ConcretifyCxt) () ExtendedASG ()
    cleanupAppNode appId (AValNode rTy (App fn args instTys cFunTy)) concretifications = do
      -- The definitive test for whether this needs cleaned up is the presence of the fn Id in the
      -- collection of type fixers
      tyFixers <- asks (R..! #tyFixers)
      case M.lookup fn tyFixers of
        Nothing -> do
          -- If it's not there it's not a node we care about. We only add
          -- projection or embedding handlers to app nodes which result from
          -- our type fixer -> app node transform.
          pure ()
        Just (TyFixerFnData tn enc _polyTyNoHandlers _compiled schema _nm kind ) -> do
          -- if the datatype the synthetic function originated from is SOP encoded, we don't need
          -- to do anything.
          when (enc == SOP) $ pure ()
          unless (enc == SOP) $ do
            -- we need to extract the "function type with handlers added" from the schema, which in this branch has to be a data schema
            (polyWithHandlers,_handlerArgPosDict) <- case schema of
                                                      SOPSchema{} -> traceError $ "SOP schema mismatch in " <> show tn <> " " <> show enc
                                                      DataSchema ty dict -> pure (ty,dict)
            let CompN _ (ArgsAndResult polyArgsWithHandlers _) = polyWithHandlers
                CompN _ (ArgsAndResult concreteArgsNoHandlers _) = cFunTy
                -- we need to get at the handlers to determine their types
                handlerFnTys = Vector.drop (Vector.length concreteArgsNoHandlers) polyArgsWithHandlers
            -- while we *really* should just record the handler type order as a vector in our TyFixerFnData (TODO: Do it),
            -- we know that they are all Comp0 identity functions with only tyvar params, so we can get what we need by doing...
            handlerIndices <- Vector.forM handlerFnTys $ \case
                                ThunkT (Comp0 ((Abstraction (BoundAt _ i)) :--:> ReturnT _)) -> pure i
                                other -> traceError $ "Encountered an invalid type when adding projection/embedding handlers: " <> show other
            -- we can mash the next two steps together. they are:
            --   1. Look up the concrete type that the tyvar it "handles" is instantiated to
            --   2. check whether that type is a representationally amorphous primitive (i.e. whether it's Int or ByteString -_- all of this
            --      for those two types!) and if so, find the `Id` corresponding to its projection or embedding (we select based on the node kind
            --      in our TyFixerFnData)
            -- NOTE/IMPORTANT: Technically we are using computation types in a value type place here but that *shouldn't* matter.
            --                 If I'm wrong we need to insert some additional nodes to thunk the dummy handlers and then force them, but
            --                 since this is the last step before codegen we should be fine to not do that.
            projEmbedHandlers <- asks (R..! #builtinHandlers)
            identityFn <- forgetExtendedId <$> asks (R..! #identityFn)
            extraProjEmbArgs <- Vector.forM handlerIndices $ \hIndx ->
                                  case M.lookup hIndx concretifications of
                                    Nothing -> traceError $ "Could not locate a concretification for tyvar " <> show hIndx
                                                            <> " while resolving projection/embedding types for "
                                                            <> show tn <> " " <> show kind
                                    Just (BuiltinFlat bi) -> case M.lookup bi projEmbedHandlers of
                                      Nothing -> pure $ AnId identityFn
                                      Just repPolyHandler -> case kind of
                                        MatchNode -> pure . AnId $ project repPolyHandler
                                        CataNode -> pure . AnId $ project repPolyHandler
                                        IntroNode -> pure . AnId $ embed repPolyHandler
                                    _ -> pure $ AnId identityFn 
            -- We don't actually *have* to fix the concretified type annotation in the app node, but
            -- it doesn't really hurt if we do and might save us during debugging
            let newConcreteFunTy = cleanup $ substCompT vacuous  (M.mapKeys (BoundAt Z) concretifications) polyWithHandlers
                newNode = AValNode rTy $ AppInternal fn (args <> extraProjEmbArgs) instTys newConcreteFunTy
            -- again we don't *have* to do this but we might as well keep things correct.
            -- This just sets the synthetic function node to have the correct type.
            coerceCompNodeTy fn polyWithHandlers
            eInsert appId newNode
    cleanupAppNode _ node _ = traceError $ "Passed something that wasn't an app node to cleanupAppNode: " <> show node

    coerceCompNodeTy :: Id -> CompT AbstractTy -> RWS (Rec ConcretifyCxt) () ExtendedASG ()
    coerceCompNodeTy i compT = do
      eid <- resolveExtended i
      eNodeAt eid >>= \case
        ACompNode _compT node -> eInsert eid (ACompNode compT node)
        _ -> pure ()

    resolveRigid :: AbstractTy -> RWS (Rec ConcretifyCxt) () ExtendedASG (AbstractTy, ValT Void)
    resolveRigid rgd@(BoundAt db i) = do
      bindingLam <- dbBindingSite db
      context <- asks (R..! #context)
      findClosestAppWithFn bindingLam >>= \case
        Nothing -> traceError $ "No app node in our app path found with function id: " <> show bindingLam
        Just appId -> case M.lookup appId context >>= M.lookup i of
          Nothing -> traceError $ "Could not resolve rigid " <> show rgd <> ", no type found in context"
          Just res -> pure (rgd,res)
     where
       findClosestAppWithFn :: LambdaId -> RWS (Rec ConcretifyCxt) () ExtendedASG (Maybe AppId)
       findClosestAppWithFn lid = do
         appPath <- asks (R..! #appPath)
         appsWithNodes <- traverse (\x@(AppId i') -> (x,) <$> eNodeAt i') appPath
         let matchesLam = \case
               AValNode _ (App fn _ _ _) -> LambdaId fn == lid
               _ -> False
         pure $ fst <$> Vector.find (matchesLam . snd) appsWithNodes

    go :: ExtendedId ->  RWS (Rec ConcretifyCxt) () ExtendedASG ()
    go eid = eNodeAt eid >>= \case
      AnError -> pure ()
      ACompNode _compT compNode -> case compNode of
        Lam bRef -> do
          let lamId = LambdaId $ forgetExtendedId eid
          local (mapField #callPath (Vector.cons lamId)) $ goRef bRef
        Force fRef -> goRef fRef
        _ -> pure ()
      appNode@(AValNode _valT valNode) -> case valNode of
        (App fn args _instTys cFunTy) -> do
          {- There have to be two branches here:
               1. If  there aren't any rigids remaining in the "concrete as possible"
                  type ('ty' here) then we just log the result and move to the children

               2. If there ARE rigids remaining, we need to resolve them.
                  The old procedure for doing this is super convoluted but I think we can take a
                  shortcut and do something like:
                    - We can get the ID of the lambda by indexing into our callPath
                    - Then we find the app that fixes the types by looking for the first
                      application above us (i.e. in the appPath) which contains that lambda as
                      a fn.

                      I am pretty sure that app has to be the one that determines the concretifications.
                      But REVIEW check with Koz.
                    - Then we look up the entry for that Lambda,App pair and we're done with the
                      "hard" part (we still have to do some annoying type/term surgery but that's just tedious)

              That should work. We have to be carefuly to only recurse with the
              current AppId cons'd onto the local reader context for the
              FUNCTION PART of the recursion. The appChain is supposed to *mean* something like:
              All of the applications above us which might determine the concrete types of our rigids.
              An application can only concretify the type of the function.
          -}
          polyFnTy  <- unsafeFnTy fn
          fnEid <- resolveExtended fn
          let CompN cnt (ArgsAndResult polyArgs _) = polyFnTy
              bVars = Vector.toList $ countToAbstractions cnt
              CompN _ (ArgsAndResult monoArgs _) = cFunTy
              subs = flip runReader 0 $ getInstantiations bVars (Vector.toList polyArgs) (Vector.toList monoArgs)
              (concrete,nonConcrete) = M.partition isConcrete subs
              here = AppId . forgetExtendedId $ eid
          if null nonConcrete
            then do
              let thisContext = M.mapKeys (\(BoundAt _ i) -> i) $ assertConcrete <$> concrete
                  localF :: Rec ConcretifyCxt -> Rec ConcretifyCxt
                  localF = mapField #context (M.insert here thisContext)
                           . mapField #appPath (Vector.cons here)
              local localF $ go fnEid
              traverse_ goRef args
              cleanupAppNode eid appNode thisContext
            else do
              let rigids = collectRigids cFunTy
              {- This is a map from the *lingering abstraction in this app node* to a concrete type.
                 That doesn't by itself, give us what we want, since the index of the tyvar bound by
                 the function of the app we're examining is totally unrelated to the index of the rigid
                 in the lambda that binds IT.

                 Another way of putting this: We know that there is a rigid in our conrete-as-possible-up-to-now type,
                 and we know what the rigid resolves to, but what we do not yet know is what exactly OUR type
                 variable gets concretified to to).

                 We cannot assume that the type variable we're trying to solve necessarily concretifies to
                 a rigid directly. For example, if have an identity function like

                 `id :: forall a. a -> a`

                 And we apply it to `Maybe r3` (where r3 is a rigid type variable bound in an enclosing lambda),
                 then. We'd end up with the substitution `a ~ Maybe r3`.

                 So what we have to do here is to substitute into the "non-concrete" types using our rigidsResolved
                 dictionary. Note that the keys in this are abstractions that occur in the function type HERE.
                 Following our example for clarity, we have:

                   nonConcrete = [a := Maybe r3]
                   rigidsResolved = [r3 := Int]   -- Int is just an example concrete type

                 And if we substitute into the elements of nonConcrete using rigidsResolved, we should get
                   [a := Maybe Int]
              -}
              rigidsResolved <- M.fromList <$> traverse resolveRigid (S.toList rigids)
              let resolvedNonConcrete = M.mapKeys (\(BoundAt _ i) -> i) $
                                          assertConcrete
                                          . runSubst 0 id (vacuous <$> rigidsResolved)
                                          <$> nonConcrete
                  sanitizedConcrete = M.mapKeys (\(BoundAt _ i) -> i) $ assertConcrete <$> concrete
                  thisContext = resolvedNonConcrete <> sanitizedConcrete
                  localF = mapField #context (M.insert here thisContext)
                               . mapField #appPath (Vector.cons here)
              local localF $ go fnEid
              traverse_ goRef args
              cleanupAppNode eid appNode thisContext

        Thunk child -> resolveExtended child >>= go
        -- This is only meant to be used on ASGs that have undergone the
        -- TypeFixerNode -> AppNode transformation, so there shouldn't be any other possibilities
        -- here. (We can ignore literals)
        _ -> pure ()
