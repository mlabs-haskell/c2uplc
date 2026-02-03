{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Transform.Cata where

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Covenant.Type (
    AbstractTy (BoundAt),
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (Comp0, Comp2, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (BuiltinStrategy),
    TyName (TyName),
    ValT (..),
    tyvar,
 )

import Control.Monad.Except (runExceptT)
import Covenant.Data (DatatypeInfo (DatatypeInfo), mkCataFunTy)
import Covenant.DeBruijn (DeBruijn (..))
import Covenant.Index (Count, intCount, intIndex, ix0, ix1, ix2)
import Covenant.MockPlutus (
    PlutusTerm,
    pApp,
    pCase,
    pForce,
    pLam,
    pVar,
 )
import Data.Foldable (
    foldl',
 )
import Data.Maybe (fromJust)
import Data.Text (Text)
import Data.Text qualified as T
import Optics.Core (preview, review, view)

import Control.Monad.RWS.Strict (MonadReader, MonadState)
import Covenant.CodeGen.Stubs (MonadStub)
import Covenant.Transform.Common
import Covenant.Transform.Pipeline.Common
import Covenant.Transform.Pipeline.Monad
import Data.Kind (Type)
import Data.Map.Strict (Map)

-- NOTE: 'Natural' and 'Negative' + The ByteString cata don't really fit in here
--       so we have to add them manually when we call this
--  (TODO: Make sure we do that )
-- A 'Nothing' result here indicates that the type isn't recursive
mkCatamorphism ::
    forall (m :: Type -> Type).
    ( MonadStub m
    , MonadReader Datatypes m
    , MonadState RepPolyHandlers m
    ) =>
    TyName ->
    m (Maybe TyFixerFnData)
mkCatamorphism tn@(TyName tyNameInner) = lookupDatatypeInfo tn >>= go
  where
    go :: DatatypeInfo AbstractTy -> m (Maybe TyFixerFnData)
    go (DatatypeInfo OpaqueData{} _ _ _) = pure Nothing -- have to catch opaques here since they technically have a builtin strategy
    go (DatatypeInfo (DataDeclaration _ _ _ enc@(BuiltinStrategy _)) _ _ _) = builtinCataForm tyNameInner enc
    go dtInfo = case view #originalDecl dtInfo of
        OpaqueData{} -> pure Nothing
        nonOpaqueDecl ->
            if not (isRecursiveDatatype nonOpaqueDecl)
                then pure Nothing
                else case runExceptT (mkCataFunTy nonOpaqueDecl) of
                    {- First thing: We need to get ahold of the Cata Fn type. This is just the BB form with a
                       datatype argument prepended, so, for `List`, it would be something like:
                       `forall a r. List a -> r -> (a -> r -> r) -> r`

                       We don't have a "is this type actually recursive" check here, but that SHOULD be caught well
                       before this point.
                    -}
                    Nothing ->
                        error $
                            "Could not construct valid catamorphism function type for type: "
                                <> T.unpack tyNameInner
                    Just eCataFunTy -> case eCataFunTy of
                        Left bbfErr ->
                            error $
                                "Error could not create a catamorphism function. Invalid datatype. BBF Error: "
                                    <> show bbfErr
                        Right (unsafeUnThunk -> cataFunTy) -> do
                            let enc = view #datatypeEncoding nonOpaqueDecl
                            let schema = mkTypeSchema False enc cataFunTy
                                cataFunName = "cata_" <> tyNameInner
                            compiled <- pFix =<< genCataPLC cataFunTy cataFunName enc schema
                            let here =
                                    TyFixerFnData
                                        { mfTyName = tn
                                        , mfEncoding = enc
                                        , mfPolyType = cataFunTy
                                        , mfCompiled = compiled
                                        , mfTypeSchema = schema
                                        , mfFunName = cataFunName
                                        , mfNodeKind = CataNode
                                        }
                            pure . Just $ here
    genCataPLC ::
        CompT AbstractTy ->
        Text ->
        DataEncoding ->
        TypeSchema ->
        m PlutusTerm
    -- \* TODO/FIXME: We really need to check whether it has a builtin encoding first and process that separately. Most of what we do here isn't useful for those.
    genCataPLC (CompN cataFnCount (ArgsAndResult origCataFnArgs _)) nameBase _enc schema = do
        {- NOTE: This is a bit different than the other cases. Here, a cata function will have a type like:
                   `forall a r. List a -> r -> (a -> r -> r) -> r` (ignoring the extra handler arguments that come at the end)
                 But the function we are actually generating also takes a recursive "self" argument
                 with a type like `List a -> r`.

                 We're just going to ignore the "self" argument at the type level here, since it's an implementation detail which
                 never needs to be visible in the Covenant type system.

                 We do, however, have to *remember that the 'self' arg exists*, which is going to make things a bit tricky
                 when inserting handlers.
        -}
        let cataFnArgs = case schemaFnType schema of CompN _ (ArgsAndResult cataSchemaFnArgs _) -> cataSchemaFnArgs
            selfVarTextPart = "cata_" <> tyNameInner <> "_self"
            -- We need to identify the `r` variable to pass it to the machinery that inserts `self` in the correct place
            -- for data encodings
            iCount = review intCount cataFnCount
            rIndex = fromJust $ preview intIndex (iCount - 1)

        selfVarName <- freshNamePrefix selfVarTextPart
        {- This will include the self var (which we name using a special scheme to keep it distinct while debugging).

           We have to keep this in mind because it breaks some of the "symmetry" we have with `match` vis-a-vis the
           actual PLC arguments and the arguments in the Covenant function type.
        -}
        let selfVar = pVar selfVarName
        lamArgNames <- Vector.cons selfVarName <$> genLambdaArgNames nameBase cataFnArgs
        let lamArgVars = pVar <$> lamArgNames
            {- As with `match`, this is a Haskell-level function which takes the body of a series of nested lambas as an argument
               and returns the complete lambda.
            -}
            lamBuilder :: PlutusTerm -> PlutusTerm
            lamBuilder = foldl' (\g argN -> g . pLam argN) id lamArgNames
            {- This is really the "argument" to the catamorphism but since we have quite a few other things called "arguments" here,
               I will follow the convention of `match` and refer to it as the scrutinee (even though that is kind of wrong)

               NOTE: Due to the extra self argument, we want the var at index 1, not 0. Index 0 is the self arg.
            -}
            scrutinee :: PlutusTerm
            scrutinee = lamArgVars Vector.! 1

            {- The handler functions for each arm. Again, we have to be careful here to ignore *both* the "self" argument and the scrutinee.
            -}
            armHandlers :: Vector PlutusTerm
            armHandlers =
                let numHandlers = Vector.length origCataFnArgs - 1 -- since we add 'self' in this module, we only subtract one, as we are working from the generated cata type
                -- the handlers are always going to occur like: \self scrutinee handler1 handler2...
                -- so we want to start the slice at index 2
                 in Vector.slice 2 numHandlers lamArgVars

            armHandlerTypes :: Vector (ValT AbstractTy)
            armHandlerTypes =
                -- HERE we're slicing the vector of the function signature for the cata function type, so we want to start
                -- at index 1 (which will only chop the scrutinee type) instead of 2, as above with the variables.
                -- Since there are no projection handler args in the original function type, we can take a shortcut here and
                -- just drop the first element of the vector of cata fn arg types.
                Vector.drop 1 origCataFnArgs

            insertForce :: (ValT AbstractTy, PlutusTerm) -> (ValT AbstractTy, PlutusTerm)
            insertForce (v, t) = case v of
                ThunkT{} -> (v, pForce t)
                _ -> (v, t)

            typedHandlers :: Vector (ValT AbstractTy, PlutusTerm)
            typedHandlers = insertForce <$> Vector.zip armHandlerTypes armHandlers
        case schema of
            SOPSchema _ -> do
                -- \*Conceptually* this is simple. E.g. for List (pretend it's SOP encoded here) we want to generate something like:
                --
                --            \self aList fNil fCons -> case aList of
                --              Nil -> fNil
                --              Cons x xs -> fCons x (self xs)
                --
                --         The implementation is a bit tricky though. We need to detect the recursive calls. I'm not sure what the *best*
                --         way to do that is, but something like this should work well enough:
                --           1. We ascertain the number of type variables bound by the original generated catamorphism function.
                --              This won't change w/ the addition of 'self' (which we ignore at the type level anyway) or
                --              the projection handlers.
                --           2. Keeping track of our variable context, we look for variables *in Thunk handlers* that have the type of the
                --              *last* type variable introduced in the generated catamorphism type.
                --
                --           REVIEW/NOTE: I *think* that we can take a shortcut here and assume that we're always working "one DB level down" from the
                --                        binding context. We don't allow data constructors to take function type parameters, so we should always be looking for a
                --                        `Tyvar (S Z) (...index of last tyvar bound...)` in thunks.
                --

                {- These "wrapped" handlers add the recursive calls to `self` where needed. For example (because this is horrendously complex):

                   If the original handler is `fCons` for the list datatype, we will end up with a function like:
                     `\x xs -> fCons x (self xs)`
                   Which is suitable for deconstructing a SOP encoded recursive type.
                -}
                wrappedHandlers <- traverse (uncurry (mkWrappedHandlerSOP selfVar cataFnCount)) typedHandlers
                pure . lamBuilder $ pCase scrutinee wrappedHandlers
            DataSchema _ handlerArgPosDict -> do
                let resolveShim = resolvePolyRepHandler CataNode handlerArgPosDict lamArgVars (Just rIndex)
                caseBody <- pCaseConstrData scrutinee typedHandlers resolveShim
                pure . lamBuilder $ caseBody

builtinCataForm ::
    forall (m :: Type -> Type).
    ( MonadStub m
    , MonadReader Datatypes m
    , MonadState RepPolyHandlers m
    ) =>
    Text ->
    DataEncoding ->
    m (Maybe TyFixerFnData)
builtinCataForm nm enc = case nm of
    "List" -> do
        let cataListTy =
                Comp2 $
                    listT a
                        :--:> b
                        :--:> thunk0 (a' :--:> b' :--:> ReturnT b')
                        :--:> ReturnT b
        pure . Just $ BuiltinTyFixer cataListTy List_Cata
    _ -> pure Nothing
  where
    thunk0 = ThunkT . Comp0

    dataT :: ValT AbstractTy
    dataT = dt "Data" []

    listT :: ValT AbstractTy -> ValT AbstractTy
    listT t = dt "List" [t]

    pairT :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
    pairT x y = dt "Pair" [x, y]

    -- The ADT not the ctor of data
    mapT :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
    mapT k v = dt "Map" [k, v]

    intT = BuiltinFlat IntegerT
    byteStringT = BuiltinFlat ByteStringT

    a = tyvar Z ix0
    b = tyvar Z ix1
    c = tyvar Z ix2

    a' = tyvar (S Z) ix0
    b' = tyvar (S Z) ix1
    c' = tyvar (S Z) ix2

    dt = Datatype

{- This is a helper used to handle code generation for the "arms" of a catamorphism.

   The first argument is a "self" variable passed in from the cata codegen function which is used to implement the
   recursive call in combination with `fix` (though we don't do that *here*).

   The second argument is the tyvar count of the (generated) catamorphism function.

   The third argument is the type of the catamorphism handler for the arm.

   The final argument is the term corresponding to the arm handler.

   This is confusing and I will forget how it works if I need to debug it, so for illustrative purposes, imagine we're operating on
   Lists. If we assume that:

     - `self` is the name of the self var to facilitate recursion with `fix`.
     - The list is a normal list and so takes on tyvar parameter, yielding a count of 2 (the `r` gets added by our machinery)
     - We're on the `Cons` arm, so the handler type is `a -> r -> r` (where `a` and `r` are arbitrary but distinct type vars)
     - the name of the original handler provided (e.g. via the `cata` ASG helper) is `fCons`

   Then `mkWrappedHandlerSOP self (Count 2) (a -> r -> r) fCons` should give us:
     `\x xs -> fCons x (self xs)`

   NOTE to self: If something weird breaks, we can probably test this part in isolation, which might be useful for debugging.

   NOTE: We have to do this a bit differently because we DO NOT want to insert projections or embeddings for statically known types.
         In non-cata cases, we don't have any kind of "handlers" to insert, but here we have to account for the application of
         `self` to recursive calls.
-}
mkWrappedHandlerSOP ::
    forall (m :: Type -> Type).
    ( MonadStub m
    , MonadReader Datatypes m
    , MonadState RepPolyHandlers m
    ) =>
    PlutusTerm -> Count "tyvar" -> ValT AbstractTy -> PlutusTerm -> m PlutusTerm
mkWrappedHandlerSOP self cataFnCount armHandlerTy armHandlerTerm = case armHandlerTy of
    -- The count of this function HAS to be 0, we forbid polymorphic handlers (somewhere). REVIEW: Where?
    ThunkT (CompN _ (ArgsAndResult armHandlerArgTys _)) -> do
        -- First thing: We're going to need another lambda builder with a # of vars == the
        --              # of arguments to the handler, since we're wrapping the arm handler.
        newHandlerLamArgNames <- genLambdaArgNames "arm_handler_arg" armHandlerArgTys
        let newHandlerLamVars = pVar <$> newHandlerLamArgNames
            lamBuilder = foldl' (\g argN -> g . pLam argN) id newHandlerLamArgNames
            typedHandlerLamArgs = Vector.zip armHandlerArgTys newHandlerLamVars
            -- Then we need to insert calls to "self" when we encounter an `r` variable that represents a recursive
            -- instance of the original parent type.
            -- In the cons branch of our list example, the handler function type is:
            --   forall a r. a -> r -> r
            -- If we specify term vars (x :: a), (y :: r), this should yield
            -- [x, self r]
            lamArgsWithSelfCalls = flip Vector.map typedHandlerLamArgs $ \(argTy, argTerm) ->
                if isR argTy
                    then self `pApp` argTerm
                    else argTerm
        -- Since this is the SOP generator, all we need to do now is to return the wrapped lambda handler for this arm.
        pure . lamBuilder $ foldl' pApp armHandlerTerm lamArgsWithSelfCalls
    _anythingElse ->
        -- Anything other than a thunk means we're working with a 0 argument constructor and so cannot do anything except
        -- return the handler itself.
        pure armHandlerTerm
  where
    -- Something imporant to keep in mind: There is ALWAYS at least one type variable in the cata fn type
    -- (the "return type var"). So we know that iCount MUST always be > 0.
    iCount = review intCount cataFnCount
    rIndex = fromJust $ preview intIndex (iCount - 1)

    isR :: ValT AbstractTy -> Bool
    isR (Abstraction (BoundAt _ indx)) = indx == rIndex
    isR _ = False

{- Strictly we don't need this, we could just examine every ASG node and check whether
   a catamorphism for the type we're concerned with is used, or we could drive this process by
   ASG node inspection instead of doing it "all at once, for every datatype". But that's kind of awkward,
   and I think it's just easier to check whether the type is recursive.
-}
isRecursiveDatatype :: DataDeclaration AbstractTy -> Bool
isRecursiveDatatype OpaqueData{} = False
isRecursiveDatatype (DataDeclaration tn cnt ctors _enc) = any check ctors
  where
    tyVarArgs :: Vector (ValT AbstractTy)
    tyVarArgs = countToTyVars cnt

    check :: Constructor AbstractTy -> Bool
    check (Constructor _ args) = any (isRec tyVarArgs) args

    bump :: ValT AbstractTy -> ValT AbstractTy
    bump = \case
        Abstraction (BoundAt db i) -> Abstraction (BoundAt (S db) i)
        other -> other

    isRec :: Vector (ValT AbstractTy) -> ValT AbstractTy -> Bool
    isRec tyVars = \case
        -- We don't allow polymorphic fn arguments to constructors.
        -- ...we might not allow any fn arguments, but I can't remember.
        -- At any rate, if we do, they have to be Comp0s, which makes this easier
        -- I *think* we only care about possible occurrences in the arguments? I'm not 100%
        -- sure but I think that recursion in the result type would be contravariant and therefore
        -- not something we have to care about, NOTE ask Koz
        ThunkT (CompN _ (ArgsAndResult args _)) ->
            let tyVars' = fmap bump tyVars
             in any (isRec tyVars') args
        Datatype tn' dtArgs -> (tn' == tn && dtArgs == tyVars) || any (isRec tyVars) dtArgs
        _ -> False
