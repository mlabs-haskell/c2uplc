{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Use <$>" -}
-- Seriously WTF this makes things so much uglier!
module Covenant.ArgDict where

import Data.Word (Word64)

import Data.Kind (Type)

import Data.Map (Map)
import Data.Map qualified as M

import Data.Text qualified as T

import Data.Vector (Vector)
import Data.Vector qualified as Vector

import Control.Monad.RWS.Strict (MonadTrans (lift), RWS, ask, evalRWS, get, local, modify)

import Covenant.ASG (
    ASG,
    ASGNode (ACompNode, AValNode, AnError),
    BoundTyVar,
    CompNodeInfo (Builtin1, Builtin2, Builtin3, Builtin6, Force, Lam),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (App, Cata, DataConstructor, Lit, Match, Thunk),
    nodeAt,
    topLevelId,
 )
import Covenant.Type (
    AbstractTy (BoundAt),
    CompT (CompN),
    CompTBody (ArgsAndResult),
    ConstructorName (ConstructorName),
    TyName (TyName),
    ValT (..),
 )

import Covenant.DeBruijn (DeBruijn (Z), asInt)
import Covenant.ExtendedASG
import Covenant.Index (Index, intCount, intIndex)
import Covenant.Test (Arg (UnsafeMkArg), BoundTyVar (BoundTyVar), Id (UnsafeMkId))

import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Covenant.Constant (AConstant (..))
import Covenant.Transform.TyUtils
import Data.Maybe (fromJust)
import Data.Void (Void, vacuous)
import Data.Wedge
import Optics.Core (preview, review)
import PlutusCore.Name.Unique (Name (Name), Unique (Unique))
import Prettyprinter

-- I need some of this to make debugging faster (the time spent writing this will save me
-- more time debugging than it takes), it should be somewhere else eventually

prettyLam :: forall ann. Doc ann -> Doc ann -> Doc ann
prettyLam var body =
    align . group $
        "\\" <> var <+> "->" <> line <> nest 2 body

data PrettyContext ann
    = PrettyContext
        (Vector Id) -- Lambda IDs
        (Map Id (Vector (Doc ann)))

matchLike :: Doc ann -> Doc ann -> Vector (Doc ann) -> Doc ann
matchLike prefix scrut handlers =
    group $
        prefix
            <+> scrut
            <+> line
            <+> group (indent 2 . braces . vcat . punctuate ";" . Vector.toList $ handlers)

pName :: Name -> String
pName (Name txtPart _) = T.unpack txtPart

pVec :: forall a. (a -> String) -> Vector a -> String
pVec f v = "[" <> foldr (\x acc -> if null acc then f x else f x <> ", " <> acc) "" (Vector.toList v) <> "]"

pValTs :: Vector (ValT AbstractTy) -> String
pValTs = show . list . Vector.toList . fmap (prettyValT False)

pValT :: ValT AbstractTy -> String
pValT = show . prettyValT False

prettyValT :: forall ann. Bool -> ValT AbstractTy -> Doc ann
prettyValT needParens = \case
    Abstraction (BoundAt db i) ->
        let db' = review asInt db
            i' = review intIndex i
         in "a_" <> pretty db' <> "#" <> pretty i'
    ThunkT compT -> angles $ prettyCompT compT
    BuiltinFlat biFlat -> viaShow biFlat
    Datatype (TyName tn) args ->
        let unary = null args
            args' = hsep . map (prettyValT True) . Vector.toList $ args
         in if unary
                then pretty tn
                else
                    if needParens
                        then
                            parens
                                (pretty tn <+> args')
                        else pretty tn <+> args'

pCompT :: CompT AbstractTy -> String
pCompT = show . prettyCompT

prettyCompT :: forall ann. CompT AbstractTy -> Doc ann
prettyCompT (CompN cnt (ArgsAndResult args result))
    | null tyVars = mkFn
    | otherwise = mkForall <> "." <+> mkFn
  where
    tyVars = countToTyVars cnt
    mkForall =
        ("forall" <+>)
            . hsep
            . Vector.toList
            $ Vector.imap
                (\i _ -> "a_0" <> "#" <> pretty i)
                tyVars
    pArgs = Vector.toList $ prettyValT False <$> args
    pRes = "!" <> prettyValT True result
    mkFn = hsep $ punctuate " ->" (pArgs <> [pRes])

ppASG :: Map Id ASGNode -> String
ppASG m = show $ runReaderT (simplePrettyASG getNode top (m M.! top)) (PrettyContext mempty mempty)
  where
    top = fst $ M.findMax m
    getNode = flip M.lookup m

crudePrettyASG' :: Map Id ASGNode -> String
crudePrettyASG' = show . crudePrettyASG

crudePrettyASG :: forall ann. Map Id ASGNode -> Doc ann
crudePrettyASG nodes =
    "["
        <> hardline
        <> (group (indent 2 (vcat . fmap (uncurry go) . M.toList $ nodes)))
        <> "]"
  where
    go :: Id -> ASGNode -> Doc ann
    go i node =
        align . group $
            ( vcat
                [ prettyId i <+> ":" <+> prettyNodeTy node
                , prettyId i <+> "=" <+> prettyNodeBody node
                ]
                <> hardline
            )

    prettyId (UnsafeMkId i) = "id_" <> pretty i

    prettyRef = \case
        AnArg (UnsafeMkArg db indx ty) ->
            let db' = review asInt db
                indx' = review intIndex indx
                pty = prettyValT False ty
             in parens $ "arg" <> pretty db' <> brackets (pretty indx') <+> ":" <+> pty
        AnId i -> prettyId i

    prettyInstTys :: [Wedge BoundTyVar (ValT Void)] -> Doc ann
    prettyInstTys = hsep . map goInstTy
      where
        goInstTy :: Wedge BoundTyVar (ValT Void) -> Doc ann
        goInstTy = \case
            Nowhere -> "@NO_INST"
            Here (BoundTyVar db indx) ->
                let db' = review asInt db
                    indx' = review intIndex indx
                 in "@" <> parens ("tyVar" <> pretty db' <> brackets (pretty indx'))
            There t -> "@" <> prettyValT True (vacuous t)

    prettyLamCxt :: CompT AbstractTy -> Doc ann
    prettyLamCxt (CompN _ (ArgsAndResult args _)) = hsep . Vector.toList . Vector.imap (\i -> parens . goCxt i) $ args
      where
        goCxt :: Int -> ValT AbstractTy -> Doc ann
        goCxt indx t = "arg0" <> brackets (pretty indx) <+> ":" <+> prettyValT False t

    prettyNodeBody :: ASGNode -> Doc ann
    prettyNodeBody = \case
        AnError -> "ERROR"
        AValNode _ valInfo -> case valInfo of
            Lit aConst -> case aConst of
                AnInteger i -> pretty i
                ABoolean b -> pretty b
                AUnit -> pretty ()
                AByteString bs -> viaShow bs
                AString txt -> pretty txt
            App fnId args instTys concrTy ->
                let prettyFn = prettyId fnId
                    prettyArgs = prettyRef <$> Vector.toList args
                    prettyConcrFnTy = prettyCompT concrTy
                    appBlob = align . group . encloseSep "" "" " # " $ (prettyFn : prettyArgs)
                    instTyBlob = prettyInstTys (Vector.toList instTys)
                 in brackets appBlob
                        <+> instTyBlob
                        <+> parens prettyConcrFnTy
            Thunk child -> angles (prettyId child)
            Cata compT handlers scrut ->
                "cata"
                    <+> ("@" <> parens (prettyCompT compT))
                    <+> prettyRef scrut
                    <+> list (prettyRef <$> Vector.toList handlers)
            DataConstructor (TyName tn) (ConstructorName cn) args ->
                pretty tn <> "." <> pretty cn <+> (align . group . encloseSep "" "" " " $ (prettyRef <$> Vector.toList args))
            Match scrut args -> "match" <+> prettyRef scrut <+> list (prettyRef <$> Vector.toList args)
        ACompNode compTy compInfo -> case compInfo of
            Builtin1 bi1 -> viaShow bi1
            Builtin2 bi2 -> viaShow bi2
            Builtin3 bi3 -> viaShow bi3
            Builtin6 bi6 -> viaShow bi6
            Force forced -> "!" <> parens (prettyRef forced)
            Lam body -> "\\" <> prettyLamCxt compTy <+> "->" <+> prettyRef body

    prettyNodeTy :: ASGNode -> Doc ann
    prettyNodeTy = \case
        AnError -> "ERROR"
        AValNode t _ -> prettyValT False t
        ACompNode t _ -> prettyCompT t

-- this prints it like a Haskell expression (i.e. it's meant for "is this what we really wanted?")
-- The crude printer is better for debugging issues where you need to see everything explicitly
-- (but in a more compact form than 'Show')
simplePrettyASG ::
    forall m ann.
    (Monad m) =>
    (Id -> m ASGNode) ->
    Id ->
    ASGNode ->
    ReaderT (PrettyContext ann) m (Doc ann)
simplePrettyASG lookupNode thisId@(UnsafeMkId i) = \case
    AnError -> pure "ERROR"
    ACompNode compT compNode -> case compNode of
        Lam ref -> step compT $ \boundVars -> do
            let boundVars' = hsep $ Vector.toList boundVars
            body <- goRef ref
            pure $ prettyLam boundVars' body
        Force fRef -> ("!" <>) . parens <$> goRef fRef
        Builtin1 bi1 -> pure $ viaShow bi1
        Builtin2 bi2 -> pure $ viaShow bi2
        Builtin3 bi3 -> pure $ viaShow bi3
        Builtin6 bi6 -> pure $ viaShow bi6
    AValNode valT valInfo -> case valInfo of
        Lit aConstant -> case aConstant of
            AnInteger i -> pure $ pretty i
            ABoolean b -> pure $ pretty b
            AUnit -> pure $ pretty ()
            AByteString bs -> pure $ viaShow bs
            AString t -> pure $ pretty t
        app@(App fn args _ _) -> do
            prettyFn <- lift (lookupNode fn) >>= simplePrettyASG lookupNode fn
            pargs <- Vector.toList <$> traverse goRef args
            pure $ align . group . encloseSep "" "" " # " $ (prettyFn : pargs)
        Thunk child -> do
            childNode <- lift $ lookupNode child
            childDoc <- simplePrettyASG lookupNode child childNode
            pure $ angles childDoc
        Cata ty handlers arg -> matchLike "cata" <$> goRef arg <*> traverse goRef handlers
        DataConstructor (TyName tn) (ConstructorName cn) args -> do
            let fnPart = pretty tn <> "." <> pretty cn
            pargs <- Vector.toList <$> traverse goRef args
            pure $ align . group . encloseSep "" "" " # " $ (fnPart : pargs)
        Match scrut handlers -> matchLike "match" <$> goRef scrut <*> traverse goRef handlers
  where
    goRef :: Ref -> ReaderT (PrettyContext ann) m (Doc ann)
    goRef = \case
        AnId argId -> lift (lookupNode argId) >>= \argNode -> simplePrettyASG lookupNode argId argNode
        AnArg (UnsafeMkArg argDb' argIx' argTy) -> do
            let argDb = review asInt argDb'
                argIx = review intIndex argIx'
                -- \$arg(db,index) is how we indicate a "rigid" term var  we can't resolve
                -- (probably b/c it points to something outside of the fragment)
                unresolvedArg = "$arg" <> tupled [pretty argDb, pretty argIx]
            PrettyContext lamStack cxt <- ask
            case lamStack Vector.!? argDb of
                Nothing -> pure unresolvedArg
                Just bindingLam -> case M.lookup bindingLam cxt of
                    Nothing -> pure unresolvedArg
                    Just boundVars -> case boundVars Vector.!? argIx of
                        Nothing -> pure unresolvedArg
                        Just v -> pure v
    step :: CompT AbstractTy -> (Vector (Doc ann) -> ReaderT (PrettyContext ann) m a) -> ReaderT (PrettyContext ann) m a
    step compT cont = do
        let vars = mkVars compT
            localF (PrettyContext lamStack cxt) = PrettyContext (Vector.cons thisId lamStack) (M.insert thisId vars cxt)
        local localF (cont vars)
    mkVars :: CompT AbstractTy -> Vector (Doc ann)
    mkVars (CompN _ (ArgsAndResult args _)) =
        Vector.imap (\argpos _ -> "x_" <> pretty i <> "#" <> pretty argpos) args

{-
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
-}
