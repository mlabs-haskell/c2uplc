{- HLINT ignore "Use if" -}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE StrictData #-}

module Covenant.Transform.Schema
  ( TypeSchema (..),
    mkTypeSchema,
    schemaFnArgs,
    schemaFnType,
  )
where

import Covenant.ArgDict (pCompT)
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (Index, intCount, intIndex)
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    DataEncoding (SOP),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    tyvar,
  )
import Data.Foldable
  ( foldl',
  )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Optics.Core (review)

trace :: forall a. String -> a -> a
trace _ x = x

{- This module contains functions (and types) for resolving the argument position of "extra handler args".

   It is much easier to understand with an example. Consider a data encoded `Maybe` type defined like:

   ```
     data Maybe a = Nothing | Just a
   ```

   This datatype has a corresponding 'match' function:

   `forall a. Maybe a -> r -> (a -> r) -> r`

   But this is a problem w/r/t representational polymorphism: We want to handle rep polymorphism by
   modifying functions to take additional arguments which represent projection/embedding functions.
   That is, we want a function type like:

   `forall a. Maybe a -> r -> (a -> r) -> (a -> a) -> r`

   NOTE: As a conceit, we "lie" about the type of the (a -> a) function we added as an extra function argument.
         Because this is a match expression, that function will be a projection (i.e. something that
         turns a data-encoded representationally polymorphous primitive, such as Integer or ByteString,
         into a "bare" Integer or Bytestring, which is what our match arms expect). So for a `match`, the
         "real" type of that function will be something like `Data -> a`. This isn't a problem, but it is
         useful/important to keep in mind.

   It's easy enough to add extra arguments for projection/embedding functions. The tricky thing is that we need to
   be able to know, during code generation, *which* tyvar is associated with *which* proj/embed handler.

   Due to some special invariants that result from working with functions known to be "isolated" (i.e. they have no
   term or type dependencies from elsewhere in the ASG and are generated purely from datatype declarations), we only have to
   care about argument INDICES here, since we cannot have an "external rigid".

   So here, we're aiming to produce a `Map (Index "tyvar") Int`, where the int represents the index into the
   vector that points at the embed/project handler for a given type. That lets us do type-directed code generation
   and insert the appropriate handlers as needed.
-}

{- The SOP case is boring, we just return the function type we're given since we don't need any other information.

   The data case:
     1. Returns the fully explicit function type, i.e., such that it includes the extra projection/embedding
        argument handlers.
     2. Returns a map that associates a type variable bound in the function type with an offset into
        the vector of arguments which points at the handler for that type.

   It is important to note that, because we only ever use this on functions generated directly from a
   datatype, the ONLY type variables will either be top level Z-indexed arguments, or (S Z) indexed arguments
   inside Comp0 thunks.

   That *ought to* entail that we don't really need to care about the DeBruijn index at all. Inside thunks arguments
   to the CompT, the DB indices are irrelevant for our purposes: There is only one scope, so we can derive all of the
   information we need from the (argument position, NOT DeBruijn) index (which indicates the order of type variable bindings).
-}
data TypeSchema
  = SOPSchema (CompT AbstractTy)
  | DataSchema (CompT AbstractTy) (Map (Index "tyvar") Int)

-- gets the CompT out of the schema
schemaFnType :: TypeSchema -> CompT AbstractTy
schemaFnType = \case
  SOPSchema compT -> compT
  DataSchema compT _ -> compT

-- gets the Args out of the CompT inside the schema
schemaFnArgs :: TypeSchema -> Vector (ValT AbstractTy)
schemaFnArgs s = case schemaFnType s of
  (CompN _ (ArgsAndResult args _)) -> args

mkTypeSchema ::
  -- "Is it an intro node?" - controls whether we expect an 'r' tyVar which we have to ignore in match/cata
  Bool ->
  DataEncoding ->
  -- The function type. This should be the
  -- "generated" function type, e.g. the thing we get
  -- from the Covenant.Data functions that create match or cata types
  -- (or whatever)
  CompT AbstractTy ->
  TypeSchema
mkTypeSchema isIntro dataEnc fnTy@(CompN tvCnt (ArgsAndResult args result)) = case dataEnc of
  SOP -> SOPSchema fnTy
  -- All of our "Builtin" types (i.e. types that we pretend are ADTs but which are really onchain primitives,
  -- such as list, pair, etc) are "morally data encoded" (in the sense that they need projections and embeddings
  -- and nothing about the builtin strategy will affect those projections or embedding), I think?
  -- We ought to be able to handle every non-SOP  case the same way.
  _builtinOrData ->
    -- if we don't have any arguments (i.e. if the thunk is just a ReturnT) then
    -- we can just return an empty map and the original function type unaltered. We need
    -- arguments to insert proj/embed handlers. Also, this lets us safely assume that the vector isn't empty
    -- going forward, which is useful to avoid out of bounds errors
    if lenOrigArgs == 0
      then DataSchema fnTy M.empty
      else
        let extraArgBundle :: (Int, Map (Index "tyvar") Int, Vector (ValT AbstractTy))
            extraArgBundle =
              -- This constructs the (a -> a) types for the extra projection/embedding arguments
              let mkProjEmbedHandlerArg :: Index "tyvar" -> ValT AbstractTy
                  mkProjEmbedHandlerArg indx =
                    -- These are always added to the top level of a function that binds the variables
                    -- being used, so we know that inside the thunk, the DB index will always be (S Z)
                    let tv = tyvar (S Z) indx
                     in ThunkT (Comp0 $ tv :--:> ReturnT tv)
               in -- There HAS to be a less convoluted way to write this, ugh. State monad?
                  foldl'
                    ( \(pos, hDict, eArgs) tv ->
                        let newHandlerDict = M.insert tv (pos + lenOrigArgs) hDict
                            newPos = pos + 1
                            handler = mkProjEmbedHandlerArg tv
                            newExtraArgs = Vector.snoc eArgs handler
                         in (newPos, newHandlerDict, newExtraArgs)
                    )
                    (0, M.empty, Vector.empty)
                    allUsedTyVarIndices
            (_, handlerDict, extraHandlerArgs) = extraArgBundle

            fnTyWithHandlers = CompN tvCnt $ ArgsAndResult (args <> extraHandlerArgs) result
            msg' = msg <> "\n  result: " <> pCompT fnTyWithHandlers
         in trace msg' $ DataSchema fnTyWithHandlers handlerDict
  where
    msg =
      "\nmkTypeSchema\n  fnTy: "
        <> pCompT fnTy
        <> "\n  allUsedTyVarIndices: "
        <> show allUsedTyVarIndices
    lenOrigArgs = Vector.length args
    allUsedTyVarIndices :: [Index "tyvar"]
    allUsedTyVarIndices =
      S.toList
        . S.fromList
        . (if isIntro then id else cleanup)
        . concatMap collectIndices
        . Vector.toList
        $ args
    -- We don't ever care about the 'r' variable - we never need to project or embed it
    -- so we can just remove it from our list. Have to be careful to only ever use this
    -- on Match/Cata since Intro doesn't have an "output tyvar"
    cleanup :: [Index "tyvar"] -> [Index "tyvar"]
    cleanup = filter (not . isR)
      where
        isR :: Index "tyvar" -> Bool
        isR indx = review intIndex indx == rIndx
        rIndx = review intCount tvCnt - 1

    collectIndices :: ValT AbstractTy -> [Index "tyvar"]
    collectIndices = \case
      Abstraction (BoundAt _ indx) -> [indx]
      ThunkT (CompN _ (ArgsAndResult args' _)) -> concatMap collectIndices $ Vector.toList args'
      BuiltinFlat _ -> []
      Datatype _ args' -> concatMap collectIndices $ Vector.toList args'

{-
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
-}
