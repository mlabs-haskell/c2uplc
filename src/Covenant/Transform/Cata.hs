{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Transform.Cata where

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
    BuiltinFlatT,
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
import Control.Monad.Reader (MonadReader, Reader, runReader)
import Control.Monad.State.Strict (MonadState (get), StateT)
import Covenant.ArgDict (idToName)
import Covenant.Data (DatatypeInfo, mkCataFunTy, mkMatchFunTy)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count2, intCount, intIndex, ix0, ix1, wordCount)
import Covenant.MockPlutus (
    PlutusTerm,
    constrData,
    listData,
    pApp,
    pCase,
    pConstr,
    pFst,
    pHead,
    pLam,
    pSnd,
    pTail,
    pVar,
    plutus_I,
    unConstrData,
    unIData,
    unListData,
 )
import Covenant.Test (Id (UnsafeMkId))
import Data.Foldable (
    find,
    foldl',
    traverse_,
 )
import Data.Kind (Type)
import Data.Maybe (fromJust, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Data.Wedge (Wedge (Here, Nowhere, There))
import Debug.Trace
import Optics.Core (ix, preview, review, view, (%))
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))

import Covenant.Transform.Common

mkCatamorphism :: TyName -> AppTransformM (Map Id TyFixerFnData)
mkCatamorphism tn@(TyName tyNameInner) = lookupDatatypeInfo tn >>= go
  where
    go :: DatatypeInfo AbstractTy -> AppTransformM (Map Id TyFixerFnData)
    go dtInfo = case view #originalDecl dtInfo of
        OpaqueData{} -> error "Do we support catamorphisms over opaque types? If we do come back and fix this later"
        nonOpaqueDecl -> case runExceptT (mkCataFunTy nonOpaqueDecl) of
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
                    newId <- nextId
                    let schema = mkTypeSchema enc cataFunTy
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
                    pure $ M.singleton newId here
    genCataPLC ::
        CompT AbstractTy ->
        Text ->
        DataEncoding ->
        TypeSchema ->
        AppTransformM PlutusTerm
    genCataPLC (CompN cataFnCount (ArgsAndResult origCataFnArgs _)) nameBase enc schema = do
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

            typedHandlers :: Vector (ValT AbstractTy, PlutusTerm)
            typedHandlers = Vector.zip armHandlerTypes armHandlers
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
mkWrappedHandlerSOP :: PlutusTerm -> Count "tyvar" -> ValT AbstractTy -> PlutusTerm -> AppTransformM PlutusTerm
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
    anythingElse ->
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
