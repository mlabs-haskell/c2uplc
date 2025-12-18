{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE ViewPatterns #-}

module Covenant.AppTransform where

import Data.Map (Map)
import Data.Map qualified as M

import Data.Set (Set)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (RWS, ask, asks, execRWS, local, modify)

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
import Covenant.Type (
    AbstractTy (BoundAt),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar,
 )

import Control.Applicative (Alternative ((<|>)))
import Control.Monad (join)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), StateT)
import Covenant.Data (DatatypeInfo, mkMatchFunTy)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count2, intCount, intIndex, ix0, ix1, wordCount)
import Covenant.MockPlutus (PlutusTerm, constrData, listData, pApp, pCase, pConstr, pFst, pHead, pLam, pSnd, pTail, pVar, plutus_I, unConstrData, unIData, unListData)
import Covenant.Test (Id (UnsafeMkId))
import Data.Foldable (find, foldl', traverse_)
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, preview, review, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

{- This records the information we need for our "mock" functions for catamorphisms/datatype intro/datatype elimination

   Specifically, it contains:
     1. The type name. For catas and matches, this is the type of the "scrutinee" being matched on, for intros it is the result
     2. The encoding. This will be useful later on.
     3. The FULLY POLYMORPHIC type of the function
     4. A PLC term corresponding to the function
     5. A token indicating which "sort" of function it is (cata/match/intro). This will also contain the "true"
        function type, which takes additional wrapper/unwrapper arguments IF THE TYPE IS DATA ENCODED.
        This is the type of the PLC term, but we "lie" about it when we replace the match/cata/intro with an app so as to use the existing machinery.
     6. The name of the function.

     Some explanation for 4: For example, if we have a data encoded Maybe type, the "false" types would be:
       match_Maybe :: forall a r. Maybe a -> r -> (a -> r) -> r
       Just :: forall a. a -> Maybe a
       Nothing :: forall a. Maybe a
       (.. maybe doesn't have a catamorphism form ...)

     But the "true" types w/ the handler arguments are:
       match_Maybe :: forall a r. Maybe a -> r -> (a -> r) -> (a -> a) -> r
       Just :: forall a. Maybe a -> (a -> a) -> a
       Nothing :: forall a. Maybe a

     In `match_Maybe` the extra argument will be either an identity function if the type is not a representationally amorphous
     primitive, or an unwrapper like `unI` or `unB` if the parameter is a representationally amorphous primitive.

     In the constructor forms (or at least the ones for non-nullary constructors), the extra arg will be an `I` or `B` wrapper.
-}
data MagicFunction
    = MagicFunction
    { mfTyName :: TyName
    , mfEncoding :: DataEncoding
    , mfPolyType :: CompT AbstractTy
    , mfCompiled :: PlutusTerm
    , mfTypeSchema :: MagicTypeSchema
    , mfFunName :: Text
    , mfNodeKind :: TyFixerNodeKind
    }

data TyFixerNodeKind = MatchNode | IntroNode | CataNode
    deriving stock (Show, Eq, Ord)

data MagicTypeSchema
    = SOPSchema (CompT AbstractTy)
    | -- The last arg is a "functionalized" map from type variables to the arg index of their "added as extra arguments" handlers
      -- To be more specific, it's a map from type variables *to the argument position of the ~~TERM~~, i.e. lambda arg, that
      -- handles them.
      -- We probably need this for all of the below "actually-an-application" things but I'm not 100% certain
      -- Quite possible we just need SOPSchema / DataSchema and that these variants are all redunant, keeping for now in case
      -- something requires special handling that I don't yet see
      DataSchema (CompT AbstractTy) (AbstractTy -> Maybe Int)

nextId :: RWS (Map TyName (DatatypeInfo AbstractTy)) () Id Id
nextId = do
    UnsafeMkId s <- get
    let new = UnsafeMkId (s + 1)
    modify $ const new
    pure new

{- NOTE: The type of the "function part" is just going to be the BBF (plus unwrappers),
         since we always apply the scrutinee and handler functions "all at once" with the
         match nodes we are transforming, and will therefore be able to concretify
         any type variables occuring in the fully polymorphic function type.

         So the type of the function for a SOP encoded `Maybe` would be:

         `forall a r. Maybe a -> r -> (a -> r) -> r`

         And for a data encoded maybe, it should ("eventually") be

         `forall a r. Maybe a -> r -> (a -> r) -> (r -> r) -> r`

         Though we are going to use the same "trick" here that we do for introduction, that is:
           - For our first pass, we will replace `match` nodes with a dummy function with
             no wrapper/unwrapper handlers
           - We will codegen a suitable function that *does* make use of handlers, and record that
             type seperately
           - *After* we use the "initial" ASG to fully concretify the types, we will do another pass
             where we will explicitly introduce the handlers as extra arguments to the function and
             apply the needed handler arguments.

         The reason for  doing things this way is that for our concretification analysis pass, we only really
         care about ensuring that all type variables are fully concretified (or concretified as far as possible).
         We need to know that to handle representational polymorphism. The "transform every type fixer into an app node"
         this is intended to make the analysis much easier (which it does), but we need to complete that analysis
         before we can determine *which* wrapper/unwrapper handlers the expanded function needs to be applied to.

         This is admittedly a bit strange, however I do not think there is an easier way to do things.

-}
-- this will return a singleton map
mkDestructorFunction :: TyName -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
mkDestructorFunction tn@(TyName tyNameInner) = do
    dtDict <- ask
    case M.lookup tn dtDict of
        Nothing -> error "Used a datatype we don't have declarations for. Should not be possible at this stage."
        Just dtInfo -> go dtInfo
  where
    go :: DatatypeInfo AbstractTy -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
    go dtInfo = do
        let ogDecl = view #originalDecl dtInfo
        case runExceptT (mkMatchFunTy ogDecl) of
            -- "Nothing" here means "Datatype is isomorphic to `Void`"
            Nothing -> pure M.empty
            Just eRes -> case eRes of
                Left bbfErr ->
                    error $
                        "Error: Could not create destructor function. Invalid datatype. BBF Error: "
                            <> show bbfErr
                Right matchFunTy -> do
                    let enc = view #datatypeEncoding ogDecl
                    newId <- nextId
                    let schema = mkSchema enc matchFunTy
                    let matchFunName = "match_" <> tyNameInner
                    compiled <- genElimFormPLC matchFunTy matchFunName enc schema

                    let here =
                            MagicFunction
                                { mfTyName = tn
                                , mfEncoding = enc
                                , mfPolyType = matchFunTy
                                , mfCompiled = compiled
                                , mfTypeSchema = schema
                                , mfFunName = matchFunName
                                , mfNodeKind = MatchNode
                                }
                    pure $ M.singleton newId here

    genElimFormPLC :: -- This is the "no handlers added" type, which is useful for us when   SOP or Constr things
        CompT AbstractTy ->
        Text ->
        DataEncoding ->
        MagicTypeSchema ->
        RWS (Map TyName (DatatypeInfo AbstractTy)) () Id PlutusTerm
    genElimFormPLC (CompN _ (ArgsAndResult origMatchFnArgs _)) nameBase enc schema = do
        -- These are the FULL arguments to the function (not the synthetic type we use for analysis),
        -- and this comes from the schema generator. This type includes projection/embedding functions, the
        --- original type does not.
        let matchFnArgs = case schema of
                SOPSchema (CompN _ (ArgsAndResult args _)) -> args
                DataSchema (CompN _ (ArgsAndResult args _)) _ -> args
        -- These are the (PLC) names of all of the arguments to the match function.
        -- E.g. for maybe they will be references to [Maybe a, r, (a -> r)]
        lamArgNames <- genLambdaArgNames nameBase matchFnArgs
        let lamArgVars = pVar <$> lamArgNames
            -- This is a function that takes a PLC lambda body for the match function and
            -- and returns a PLC lambda.
            lamBuilder :: PlutusTerm -> PlutusTerm
            lamBuilder = foldl' (\g argN -> g . pLam argN) id lamArgNames
            {- NOTE: It's important to keep in mind here that for an arbitrary ADT, the
                     generated match function has a regular structure: The scrutinee comes first, then
                     all of the branch handlers. Because each term var bound by the lambda corresponds to a type
                     arg, we can use this to derive references to each branch handler directly.
            -}
            scrutinee :: PlutusTerm
            scrutinee = pVar $ lamArgNames Vector.! 0

            -- We ignore the "extra unwrapper args" here because we're trying to get the names of the handlers for each
            -- match arm (and we have another way of looking up the unwrappers when we need to)
            branchHandlers :: Vector PlutusTerm
            branchHandlers =
                let numHandlers = Vector.length origMatchFnArgs - 1
                 in pVar <$> Vector.slice 1 numHandlers lamArgNames

        case schema of
            SOPSchema _ ->
                {- This is the easiest one. We do the only thing we could possibly do.
                -}
                pure . lamBuilder $ pCase scrutinee branchHandlers
            DataSchema _ getUnwrapperIx -> do
                -- This lets us look up the name (i.e. the var bound by our lambda) which corresponds to the
                -- projection/embedding function we need to use for a particular value with a bare tyvar type
                -- TODO/FIXME/BUG/REVIEW: Probably we need to increment the DB index here by one since we're always using this
                --                        on *branch handler argument types* here, which are always going to be "off by one DB"
                --                        Or and also REVIEW this, the function that constructs a schema might just never give us
                --                        what we need. Should be easy to fix once I have some output (and remember this note)
                let resolveUnwrapper :: ValT AbstractTy -> Maybe PlutusTerm
                    resolveUnwrapper = \case
                        Abstraction tv -> getUnwrapperIx tv >>= \hIx -> lamArgVars Vector.!? hIx
                        _anythingElse -> Nothing

                case enc of
                    SOP -> error $ "Data schema for SOP encoding when compiling match functions for " <> T.unpack tyNameInner
                    BuiltinStrategy _ -> error "TODO: Implement match fn codegen for builtin types"
                    PlutusData strat -> case strat of
                        EnumData ->
                            {- We know the scrutinee is an Int (or really a data-wrapped I 3, I think?).

                               We also know that the range of values it can take is "suitably compact", i.e., starts at 0
                               and increments by one for each additional enum constructor.

                               Because this is an enumeration, there are no arguments. All of the arm/branch handlers do not take any arguments,
                               and we don't need to do any unwrapping.

                               So this should be really straightforward. The body is just a case expression over the unwrapped (I Integer) where each
                               match arm is just some arm/branch handler argument to the function.
                            -}
                            pure . lamBuilder $ pCase (unIData scrutinee) branchHandlers
                        ProductListData ->
                            {- We know here that there is only one constructor.

                               The scrutinee is a data-encoded List, which is fairly straightforward.

                               The tricky part about this (which will recur when we handle ConstrData) is that we need to maintain awareness of
                               the (Covenant) types of the list elements so that we can insert unwrappers as needed.
                            -}
                            -- First, we need to look at the arguments of the branch handler.
                            -- If this IS A THUNK then we know this isn't a nullary product.
                            -- If it IS NOT A THUNK then we know it is a nullary product, and
                            -- we can just ignore the scrutinee entirely and return the branch value.

                            -- Since we know there is only one constructor and since the 0th index of the match function
                            -- is the scrutinee, we know the 1st index must be the handler for this single
                            -- constructor.
                            case origMatchFnArgs Vector.!? 1 of
                                Nothing ->
                                    error $
                                        "CodeGen failure while generating PLC match function for type "
                                            <> T.unpack tyNameInner
                                            <> ": No handler for single ProductListData ctor"
                                Just thisBranchHandler -> case thisBranchHandler of
                                    -- In the generated match function we do not ever construct a (ThunkT (ReturnT v))
                                    -- value, so we should be able to ignore the possibility.
                                    ThunkT (CompN _ (ArgsAndResult thisBranchHandlerArgTys _)) -> do
                                        let thisBranchHandlerTerm = lamArgVars Vector.! 1 -- this is safe here, in a roundabout way
                                            listEliminator =
                                                genFiniteListEliminator
                                                    thisBranchHandlerTerm
                                                    (unListData scrutinee)
                                                    resolveUnwrapper
                                                    (Vector.toList thisBranchHandlerArgTys)
                                        pure . lamBuilder $ listEliminator
                                    _ ->
                                        -- Anything else means we have a nullary constructor and can bypass any hard work here
                                        pure . lamBuilder $ branchHandlers Vector.! 1
                        ConstrData -> do
                            {- We can turn this into a PLC case expression if we extract the Integer scrutinee and construct branches for
                               all possible constructor indices to use in that PLC case expression. That should be both more
                               performance and easier to debug than using an if-then-else chain (due to the perf issue w/
                               builtins + the fact case is lazy)

                               For `Maybe` we'd end up with something like the following, except
                               that we won't be using real let binds (and we're ignoring unwrappers for simplicity):

                               ```
                                 \mayB handleNothing handleJust ->
                                    let (cIx, ctorArgs) = unConstr mayB
                                    in case cIx of
                                         0 -> handleNothing
                                         1 -> handleJust (head ctorArgs)
                               ```

                            -}
                            let constrDataPair = unConstrData scrutinee
                                ctorIx = pFst constrDataPair
                                ctorArgs = pSnd constrDataPair
                                getHandlerArgs :: Int -> [ValT AbstractTy]
                                getHandlerArgs i = case origMatchFnArgs Vector.! (i + 1) of -- we're traversing the branch handler terms which start at 1 in the match fn ty
                                    ThunkT (CompN _ (ArgsAndResult args _)) -> Vector.toList args
                                    -- if it's not a thunk that arm of the constructor has no arguments. I THINK
                                    _ -> []
                                plcHandlers = flip Vector.imap branchHandlers $ \i bHandler ->
                                    let theseHandlerArgs = getHandlerArgs i
                                     in genFiniteListEliminator
                                            bHandler
                                            ctorArgs
                                            resolveUnwrapper
                                            theseHandlerArgs
                            pure . lamBuilder $ pCase ctorIx plcHandlers
                        NewtypeData -> do
                            {- This is trivial-ish. We just need to check whether the single arg to the single branch handler
                               (which is what the type of the scrutinee "really is" if it's newtype encoded) needs a projection, and if so, we
                            -}
                            let thisBranchHandlerTerm = lamArgVars Vector.! 1
                                realScrutTy = case origMatchFnArgs Vector.! 1 of
                                    ThunkT (CompN _ (ArgsAndResult args _)) -> args Vector.! 0
                                    _ -> error $ T.unpack tyNameInner <> " has a newtype encoding, is not a valid newtype"
                            case resolveUnwrapper realScrutTy of
                                Nothing -> pure . lamBuilder $ pApp thisBranchHandlerTerm scrutinee
                                Just projFn -> pure . lamBuilder $ pApp thisBranchHandlerTerm (pApp projFn scrutinee)

{- Given a branch handler, a scrutinee, a way to lookup the projection function, and a list of types representing the
   Covenant types of elements, construct an expression that extracts the arguments from the handler and applies the handler
   to them.

   NOTE: This is kind of crude. It'll end up as a smorgasbord of nested calls to `head` and `tail`. We could
         probably do a lot better than this somehow? But this is the *easiest* way I can think of.
-}
genFiniteListEliminator :: -- The branch handler function as a plutus term
    PlutusTerm ->
    -- The scrutinee (or the argument list for a Constr-encoded data thing)
    PlutusTerm ->
    -- Looks up the right projection function
    (ValT AbstractTy -> Maybe PlutusTerm) ->
    -- The types of the list elements
    [ValT AbstractTy] ->
    PlutusTerm
genFiniteListEliminator branchHandler scrutinee resolveProjection elTys =
    foldl' pApp branchHandler $ genFiniteListElimArgs scrutinee elTys
  where
    genFiniteListElimArgs :: -- The "remainder" of the list (usually an application of tail to the original scrutinee)
        PlutusTerm ->
        -- the types of the remainder of the list
        [ValT AbstractTy] ->
        [PlutusTerm]
    genFiniteListElimArgs remList [] = [] -- nothing left to do
    -- \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/
    -- FIXME/TODO/REVIEW/BUG: THIS WONT WORK!!! Inside the handlers the DeBruijn index will always
    --                        Be 1 higher. We need to adjust DB indices here before we try to look up
    --                        the projection for a given ValT.
    genFiniteListElimArgs remList (t : ts) = case resolveProjection t of
        Nothing -> pHead remList : genFiniteListElimArgs (pTail remList) ts
        Just unwrapper -> pApp unwrapper (pHead remList) : genFiniteListElimArgs (pTail remList) ts

-- /\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\

mkConstructorFunctions :: TyName -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
mkConstructorFunctions tn = do
    dtDict <- ask
    case M.lookup tn dtDict of
        Nothing -> error "Used a datatype we don't have declarations for. Should not be possible at this stage."
        Just dtInfo -> case view #originalDecl dtInfo of
            DataDeclaration tn cnt ctors enc -> do
                Vector.ifoldM (go dtInfo cnt enc) M.empty ctors
            OpaqueData{} -> undefined
  where
    go ::
        DatatypeInfo AbstractTy ->
        Count "tyvar" ->
        DataEncoding ->
        Map Id MagicFunction ->
        Int ->
        Constructor AbstractTy ->
        RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Map Id MagicFunction)
    go dtInfo cnt enc acc cIx (Constructor (ConstructorName cName) argTys) = do
        let ctorFnTy = mkCtorFnTy cnt argTys
            schema = mkSchema enc ctorFnTy
            funName = cName
        newId <- nextId
        compiled <- genIntroFormPLC enc schema cIx
        let here =
                MagicFunction
                    { mfTyName = tn
                    , mfEncoding = enc
                    , mfPolyType = ctorFnTy
                    , mfCompiled = compiled
                    , mfTypeSchema = schema
                    , mfFunName = funName
                    , mfNodeKind = IntroNode
                    }
        pure $ M.insert newId here acc
      where
        genIntroFormPLC ::
            DataEncoding ->
            MagicTypeSchema ->
            Int ->
            RWS (Map TyName (DatatypeInfo AbstractTy)) () Id PlutusTerm
        genIntroFormPLC dataEnc schema ctorIx = do
            let introFnArgs = case schema of
                    SOPSchema (CompN _ (ArgsAndResult args _)) -> args
                    DataSchema (CompN _ (ArgsAndResult args _)) _ -> args
                -- these are the ARGUMENTS TO THE CONSTRUCTOR
                ctorArgs = argTys
            -- These are the NAMES OF ALL THE ARGUMENT TO THE INTRO FUNCTION. In this branch
            -- this will (almost always) contain MORE NAMES than the args to the constructor
            names <- genLambdaArgNames cName introFnArgs
            -- The names of arguments to the ctors
            let ctorArgNames = Vector.take (Vector.length ctorArgs) names
                nameTyPairs = Vector.zip ctorArgNames ctorArgs
                lamBuilder = foldl' (\g argN -> g . pLam argN) id names
            case schema of
                SOPSchema _ -> pure . lamBuilder $ pConstr (fromIntegral ctorIx) (pVar <$> ctorArgNames)
                DataSchema (CompN _ (ArgsAndResult introFnArgs _)) getHandlerIx -> do
                    let resolveHandler :: ValT AbstractTy -> Maybe Name
                        resolveHandler = \case
                            Abstraction tv -> getHandlerIx tv >>= \hIx -> names Vector.!? hIx
                            _anythingElse -> Nothing

                        handledCtorArgs = flip fmap nameTyPairs $ \(cArgNm, cArgTy) -> case resolveHandler cArgTy of
                            Nothing -> pVar cArgNm
                            Just argHandler -> pApp (pVar argHandler) (pVar cArgNm)
                    case dataEnc of
                        -- TODO: Fill in some of the helpers (plutus_I, listData, etc) and make sure you use the "right version" here
                        SOP -> error "something went horribly wrong, DataSchema w/ SOP encoding"
                        BuiltinStrategy _ -> error "TODO: Remember how to handle code generation for builtin strategies"
                        PlutusData strat -> case strat of
                            EnumData -> pure $ lamBuilder (plutus_I $ fromIntegral ctorIx)
                            ProductListData -> pure $ listData handledCtorArgs
                            ConstrData -> pure $ constrData (plutus_I $ fromIntegral ctorIx) (listData handledCtorArgs)
                            NewtypeData -> pure $ handledCtorArgs Vector.! 0

        mkCtorFnTy :: Count "tyvar" -> Vector (ValT AbstractTy) -> CompT AbstractTy
        mkCtorFnTy datatypeNumParams args =
            let result = Datatype tn (countToTyVars datatypeNumParams)
             in CompN datatypeNumParams (ArgsAndResult args result)

-- TODO/REVIEW: Maybe this needs to run in a reader to track DB levels?
mkSchema :: DataEncoding -> CompT AbstractTy -> MagicTypeSchema
mkSchema dataEnc fnTy@(CompN tvCnt (ArgsAndResult args result)) = case dataEnc of
    SOP -> SOPSchema fnTy
    BuiltinStrategy _strat ->
        error $
            "TODO: Try to remember what we would need to do here. For this (but not the codegen), "
                <> "it's probably fine to generate the same thing as for PlutusData"
    PlutusData _strat ->
        -- strategy doesn't matter HERE though it does for codegen
        -- note that we *can't* have "external" rigids here

        -- We only care about adding wrappers for types that occur as arguments.
        -- And - extra nice for us - we can just ignore thunks becaaauusssee
        -- this is data-encoded and they can't exist as params anyway. So we really just need to
        -- look for any arg that is a tyvar
        let getTyVar :: ValT AbstractTy -> Maybe AbstractTy
            getTyVar = \case
                Abstraction a -> Just a
                _ -> Nothing

            -- We need to return *something* that indicates which extra handler arg is associated w/ a particular
            -- tyvar. Not immediately sure what the best way to do this is.
            usedTypeVariables :: [AbstractTy]
            usedTypeVariables = S.toList . S.fromList . mapMaybe getTyVar . Vector.toList $ args

            lenOrigArgs = Vector.length args

            extraArgs' :: (Int, Map AbstractTy Int, Vector (ValT AbstractTy))
            extraArgs' =
                let mkHandler (BoundAt db indx) =
                        let tv = tyvar (S db) indx
                         in ThunkT (Comp0 $ tv :--:> ReturnT tv)
                 in foldl'
                        ( \(pos, handlerDict, eArgs) tv ->
                            let newHandlerDict = M.insert tv (pos + lenOrigArgs) handlerDict
                                newPos = pos + 1
                                handler = mkHandler tv
                                newEArgs = Vector.snoc eArgs handler
                             in (newPos, newHandlerDict, newEArgs)
                        )
                        (0, M.empty, Vector.empty)
                        usedTypeVariables

            (_, hDict, extraArgs) = extraArgs'

            polyFnTy :: CompT AbstractTy
            polyFnTy = CompN tvCnt $ ArgsAndResult (args <> extraArgs) result
         in DataSchema polyFnTy (`M.lookup` hDict)

genLambdaArgNames :: forall (a :: Type). Text -> Vector a -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id (Vector Name)
genLambdaArgNames nameBase = Vector.imapM genTermVarName
  where
    genTermVarName :: forall a. Int -> a -> RWS (Map TyName (DatatypeInfo AbstractTy)) () Id Name
    genTermVarName pos _ = do
        uniqueId@(UnsafeMkId i) <- nextId
        let textPart = nameBase <> "_arg" <> T.pack (show pos)
            uniquePart = Unique (fromIntegral i)
        pure $ Name textPart uniquePart

countToTyVars :: Count "tyvar" -> Vector (ValT AbstractTy)
countToTyVars cnt
    | cntI == 0 = mempty
    | otherwise = mkTV <$> Vector.fromList [0 .. (cntI - 1)]
  where
    cntI :: Int
    cntI = review intCount cnt

    mkTV :: Int -> ValT AbstractTy
    mkTV = Abstraction . BoundAt Z . fromJust . preview intIndex
