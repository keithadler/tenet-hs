{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Reading lean4export NDJSON (format major version 3): the shared name, level and expression tables, and
-- the declarations in the order the exporter wrote them.
module Tenet.Export
  ( ExportMeta (..), Tables (..), newTables, ExportDecl (..), XInd (..), XCtor (..), XRec (..), XRule (..)
  , Line (..), parseLine, exportDeclToDeclaration, exportDeclNames, exportDeclDisplay
  ) where

import Control.Exception (evaluate)
import Control.Monad (forM)
import qualified Data.ByteString as B
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Tenet.Env
import Tenet.Expr
import Tenet.Json
import Tenet.Level
import Tenet.Name
import Tenet.Table

data ExportMeta = ExportMeta { mExporter :: String, mLean :: String, mFormat :: String }

data Tables = Tables
  { tNames :: Table Name
  , tLevels :: Table Level
  , tExprs :: Table Expr
  }

newTables :: IO Tables
newTables = do
  ns <- newTable
  _ <- insertT ns 0 anonymous
  ls <- newTable
  _ <- insertT ls 0 LZero
  es <- newTable
  pure (Tables ns ls es)

data XInd = XInd
  { xiName :: Name, xiLParams :: [Name], xiType :: Expr, xiNumParams :: Int, xiNumIndices :: Int
  , xiAll :: [Name], xiCtors :: [Name], xiNumNested :: Int, xiIsRec :: Bool, xiIsUnsafe :: Bool, xiIsReflexive :: Bool }

data XCtor = XCtor
  { xcName :: Name, xcLParams :: [Name], xcType :: Expr, xcInduct :: Name, xcCidx :: Int
  , xcNumParams :: Int, xcNumFields :: Int, xcIsUnsafe :: Bool }

data XRule = XRule { xrCtor :: Name, xrNumFields :: Int, xrRhs :: Expr }

data XRec = XRec
  { xrName :: Name, xrLParams :: [Name], xrType :: Expr, xrAll :: [Name], xrNumParams :: Int, xrNumIndices :: Int
  , xrNumMotives :: Int, xrNumMinors :: Int, xrRules :: [XRule], xrK :: Bool, xrIsUnsafe :: Bool }

data ExportDecl
  = XAxiom Name [Name] Expr Bool
  | XDef DefDecl
  | XMutual [DefDecl]
  | XThm Name [Name] Expr Expr [Name]
  | XOpaque Name [Name] Expr Expr Bool [Name]
  | XQuot Name [Name] Expr QuotKind
  | XInductive [XInd] [XCtor] [XRec]

data Line
  = LMeta ExportMeta
  | LTable                 -- ^ a name, level or expression was added to the tables
  | LDecl ExportDecl

type R a = Either String a

parseLine :: Tables -> B.ByteString -> IO (R Line)
parseLine tbl bs = case parseJson bs of
  Left err -> pure (Left err)
  Right j@(JObj kvs) -> dispatch kvs j
  Right _ -> pure (Left "expected a JSON object")
  where
    has k kvs = maybe False (const True) (lookup k kvs)
    dispatch kvs j
      | has "meta" kvs = pure (LMeta <$> (field "meta" j >>= parseMeta))
      | has "in" kvs = add "name" (tNames tbl) (field "in" j >>= asInt) (parseName tbl j)
      | has "il" kvs = add "level" (tLevels tbl) (field "il" j >>= asInt) (parseLevel tbl j)
      | has "ie" kvs = add "expression" (tExprs tbl) (field "ie" j >>= asInt) (parseExpr tbl j)
      | otherwise = pure (LDecl <$> parseDecl tbl j)
    -- indices need not be dense or in order, but each may be defined only once
    add what table ei ev = case (ei, ev) of
      (Right i, Right v) -> do
        -- evaluate before storing: a lazy entry would keep its whole parsed JSON line alive until first use
        ok <- evaluate v >>= insertT table i
        pure (if ok then Right LTable else Left (what ++ " index " ++ show i ++ " is defined twice"))
      (Left err, _) -> pure (Left err)
      (_, Left err) -> pure (Left err)

parseMeta :: Json -> R ExportMeta
parseMeta j = do
  let sub a b = fieldMaybe a j >>= fieldMaybe b >>= \case JStr s -> Just (T.unpack s); _ -> Nothing
  pure (ExportMeta (fromMaybe "?" (sub "exporter" "name")) (fromMaybe "?" (sub "lean" "version")) (fromMaybe "?" (sub "format" "version")))

nameAt :: Tables -> Json -> R Name
nameAt tbl j = do
  i <- asInt j
  maybe (Left ("unknown name index " ++ show i)) Right (lookupT (tNames tbl) i)

levelAt :: Tables -> Json -> R Level
levelAt tbl j = do
  i <- asInt j
  maybe (Left ("unknown level index " ++ show i)) Right (lookupT (tLevels tbl) i)

exprAt :: Tables -> Json -> R Expr
exprAt tbl j = do
  i <- asInt j
  maybe (Left ("unknown expression index " ++ show i)) Right (lookupT (tExprs tbl) i)

namesAt :: Tables -> Json -> R [Name]
namesAt tbl j = asArray j >>= mapM (nameAt tbl)

levelsAt :: Tables -> Json -> R [Level]
levelsAt tbl j = asArray j >>= mapM (levelAt tbl)

parseName :: Tables -> Json -> R Name
parseName tbl j = case (fieldMaybe "str" j, fieldMaybe "num" j) of
  (Just s, _) -> do
    p <- field "pre" s >>= nameAt tbl
    t <- field "str" s >>= asString
    pure (mkStr p t)
  (_, Just n) -> do
    p <- field "pre" n >>= nameAt tbl
    k <- field "i" n >>= \case JNum x -> Right x; _ -> Left "expected an integer"
    pure (mkNum p k)
  _ -> Left "unknown name constructor"

parseLevel :: Tables -> Json -> R Level
parseLevel tbl j
  | Just s <- fieldMaybe "succ" j = LSucc <$> levelAt tbl s
  | Just m <- fieldMaybe "max" j = two m LMax
  | Just m <- fieldMaybe "imax" j = two m LIMax
  | Just p <- fieldMaybe "param" j = LParam <$> nameAt tbl p
  | otherwise = Left "unknown level constructor"
  where
    two m f = asArray m >>= \case
      [a, b] -> f <$> levelAt tbl a <*> levelAt tbl b
      _ -> Left "expected two levels"

binderInfoOf :: Json -> R BinderInfo
binderInfoOf j = asString j >>= \case
  "default" -> Right BDefault
  "implicit" -> Right BImplicit
  "strictImplicit" -> Right BStrictImplicit
  "instImplicit" -> Right BInstImplicit
  o -> Left ("unknown binderInfo '" ++ T.unpack o ++ "'")

parseExpr :: Tables -> Json -> R Expr
parseExpr tbl j
  | Just b <- fieldMaybe "bvar" j = BVar <$> asInt b
  | Just s <- fieldMaybe "sort" j = Sort <$> levelAt tbl s
  | Just c <- fieldMaybe "const" j = Const <$> (field "name" c >>= nameAt tbl) <*> (field "us" c >>= levelsAt tbl)
  | Just a <- fieldMaybe "app" j = App <$> (field "fn" a >>= exprAt tbl) <*> (field "arg" a >>= exprAt tbl)
  | Just l <- fieldMaybe "lam" j = binder Lam l
  | Just p <- fieldMaybe "forallE" j = binder Pi p
  | Just l <- fieldMaybe "letE" j =
      Let <$> (field "name" l >>= nameAt tbl) <*> (field "type" l >>= exprAt tbl)
          <*> (field "value" l >>= exprAt tbl) <*> (field "body" l >>= exprAt tbl)
  | Just p <- fieldMaybe "proj" j =
      Proj <$> (field "typeName" p >>= nameAt tbl) <*> (field "idx" p >>= asInt) <*> (field "struct" p >>= exprAt tbl)
  | Just n <- fieldMaybe "natVal" j = asString n >>= \s ->
      if not (T.null s) && T.all (\c -> c >= '0' && c <= '9') s then Right (mkNatLit (read (T.unpack s))) else Left ("invalid natVal '" ++ T.unpack s ++ "'")
  | Just s <- fieldMaybe "strVal" j = mkStrLit <$> asString s
  | Just m <- fieldMaybe "mdata" j = field "expr" m >>= exprAt tbl   -- metadata has no effect on type checking
  | otherwise = Left "unknown expression constructor"
  where
    binder f b = f <$> (field "name" b >>= nameAt tbl) <*> (field "binderInfo" b >>= binderInfoOf)
                   <*> (field "type" b >>= exprAt tbl) <*> (field "body" b >>= exprAt tbl)

hintsOf :: Json -> R Hints
hintsOf = \case
  JStr "opaque" -> Right HOpaque
  JStr "abbrev" -> Right HAbbrev
  j | Just r <- fieldMaybe "regular" j -> HRegular <$> asInt r
  _ -> Left "malformed hints"

safetyOf :: Json -> R Safety
safetyOf j = asString j >>= \case
  "safe" -> Right Safe
  "unsafe" -> Right Unsafe
  "partial" -> Right Partial
  o -> Left ("unknown safety '" ++ T.unpack o ++ "'")

quotKindOf :: Json -> R QuotKind
quotKindOf j = asString j >>= \case
  "type" -> Right QType
  "ctor" -> Right QCtor
  "lift" -> Right QLift
  "ind" -> Right QInd
  o -> Left ("unknown quot kind '" ++ T.unpack o ++ "'")

boolOr :: T.Text -> Json -> Bool
boolOr k j = case fieldMaybe k j of Just (JBool b) -> b; _ -> False

allOr :: Tables -> Json -> Name -> R [Name]
allOr tbl j n = case fieldMaybe "all" j of
  Just a -> namesAt tbl a
  Nothing -> Right [n]

-- | Format 3.0 wrote declarations as one-element arrays; 3.1 writes an object.
single :: String -> Json -> R Json
single kind = \case
  j@(JObj _) -> Right j
  JArr [j] -> Right j
  _ -> Left ("'" ++ kind ++ "' must be an object or a one-element array")

defOf :: Tables -> Json -> R DefDecl
defOf tbl d = do
  n <- field "name" d >>= nameAt tbl
  DefDecl n <$> (field "levelParams" d >>= namesAt tbl) <*> (field "type" d >>= exprAt tbl) <*> (field "value" d >>= exprAt tbl)
            <*> (field "hints" d >>= hintsOf) <*> (field "safety" d >>= safetyOf) <*> allOr tbl d n

parseDecl :: Tables -> Json -> R ExportDecl
parseDecl tbl j
  | Just a <- fieldMaybe "axiom" j = single "axiom" a >>= \x -> do
      n <- field "name" x >>= nameAt tbl
      XAxiom n <$> (field "levelParams" x >>= namesAt tbl) <*> (field "type" x >>= exprAt tbl) <*> pure (boolOr "isUnsafe" x)
  | Just d <- fieldMaybe "def" j = case d of
      JArr ds | length ds /= 1 -> XMutual <$> mapM (defOf tbl) ds
      _ -> single "def" d >>= fmap XDef . defOf tbl
  | Just o <- fieldMaybe "opaque" j = single "opaque" o >>= \x -> do
      n <- field "name" x >>= nameAt tbl
      XOpaque n <$> (field "levelParams" x >>= namesAt tbl) <*> (field "type" x >>= exprAt tbl) <*> (field "value" x >>= exprAt tbl)
                <*> pure (boolOr "isUnsafe" x) <*> allOr tbl x n
  | Just t <- fieldMaybe "thm" j = single "thm" t >>= \x -> do
      n <- field "name" x >>= nameAt tbl
      XThm n <$> (field "levelParams" x >>= namesAt tbl) <*> (field "type" x >>= exprAt tbl) <*> (field "value" x >>= exprAt tbl) <*> allOr tbl x n
  | Just q <- fieldMaybe "quot" j = single "quot" q >>= \x -> do
      n <- field "name" x >>= nameAt tbl
      XQuot n <$> (field "levelParams" x >>= namesAt tbl) <*> (field "type" x >>= exprAt tbl) <*> (field "kind" x >>= quotKindOf)
  | Just ind <- fieldMaybe "inductive" j = do
      let either' a b = maybe (field b ind) Right (fieldMaybe a ind)
      tys <- either' "types" "inductiveVals" >>= asArray >>= mapM (\t -> do
        n <- field "name" t >>= nameAt tbl
        XInd n <$> (field "levelParams" t >>= namesAt tbl) <*> (field "type" t >>= exprAt tbl)
               <*> (field "numParams" t >>= asInt) <*> (field "numIndices" t >>= asInt)
               <*> (field "all" t >>= namesAt tbl) <*> (field "ctors" t >>= namesAt tbl)
               <*> pure (either (const 0) id (maybe (Left "") asInt (fieldMaybe "numNested" t)))
               <*> pure (boolOr "isRec" t) <*> pure (boolOr "isUnsafe" t) <*> pure (boolOr "isReflexive" t))
      cts <- either' "ctors" "constructorVals" >>= asArray >>= mapM (\c -> do
        n <- field "name" c >>= nameAt tbl
        XCtor n <$> (field "levelParams" c >>= namesAt tbl) <*> (field "type" c >>= exprAt tbl) <*> (field "induct" c >>= nameAt tbl)
                <*> (field "cidx" c >>= asInt) <*> (field "numParams" c >>= asInt) <*> (field "numFields" c >>= asInt)
                <*> pure (boolOr "isUnsafe" c))
      rcs <- either' "recs" "recursorVals" >>= asArray >>= mapM (\r -> do
        n <- field "name" r >>= nameAt tbl
        rules <- field "rules" r >>= asArray >>= mapM (\ru ->
          XRule <$> (field "ctor" ru >>= nameAt tbl) <*> (field "nfields" ru >>= asInt) <*> (field "rhs" ru >>= exprAt tbl))
        XRec n <$> (field "levelParams" r >>= namesAt tbl) <*> (field "type" r >>= exprAt tbl) <*> (field "all" r >>= namesAt tbl)
               <*> (field "numParams" r >>= asInt) <*> (field "numIndices" r >>= asInt) <*> (field "numMotives" r >>= asInt)
               <*> (field "numMinors" r >>= asInt) <*> pure rules <*> pure (boolOr "k" r) <*> pure (boolOr "isUnsafe" r))
      pure (XInductive tys cts rcs)
  | otherwise = Left "unknown declaration kind"

-- | Rebuild the declaration Lean's elaborator handed to the kernel: for an inductive block, types and constructors only.
exportDeclToDeclaration :: ExportDecl -> Either String Declaration
exportDeclToDeclaration = \case
  XAxiom n lps ty u -> Right (DAxiom n lps ty u)
  XDef d -> Right (DDef d)
  XMutual ds -> Right (DMutual ds)
  XThm n lps ty v a -> Right (DThm n lps ty v a)
  XOpaque n lps ty v u a -> Right (DOpaque n lps ty v u a)
  XQuot {} -> Right DQuot
  XInductive tys cts _ -> case tys of
    [] -> Left "exported inductive block has no types"
    (first : _) -> do
      its <- forM tys $ \t -> do
        cds <- forM (xiCtors t) $ \cn -> case filter ((== cn) . xcName) cts of
          (c : _) -> Right (CtorDecl (xcName c) (xcType c))
          [] -> Left ("exported inductive '" ++ showName (xiName t) ++ "' lists constructor '" ++ showName cn ++ "' but the block does not define it")
        Right (IndType (xiName t) (xiType t) cds)
      Right (DInductive (IndDecl (xiLParams first) (xiNumParams first) its (xiIsUnsafe first)))

exportDeclNames :: ExportDecl -> [Name]
exportDeclNames = \case
  XAxiom n _ _ _ -> [n]
  XDef d -> [dName d]
  XMutual ds -> map dName ds
  XThm n _ _ _ _ -> [n]
  XOpaque n _ _ _ _ _ -> [n]
  XQuot n _ _ _ -> [n]
  XInductive ts cs rs -> map xiName ts ++ map xcName cs ++ map xrName rs

exportDeclDisplay :: ExportDecl -> (String, Name)
exportDeclDisplay = \case
  XAxiom n _ _ _ -> ("axiom", n)
  XDef d -> ("def", dName d)
  XMutual ds -> ("mutual def", case ds of (d : _) -> dName d; [] -> anonymous)
  XThm n _ _ _ _ -> ("thm", n)
  XOpaque n _ _ _ _ _ -> ("opaque", n)
  XQuot n _ _ _ -> ("quot", n)
  XInductive ts _ _ -> ("inductive", case ts of (t : _) -> xiName t; [] -> anonymous)
