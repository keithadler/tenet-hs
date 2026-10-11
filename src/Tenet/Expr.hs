{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
{-# LANGUAGE MagicHash #-}
-- | Kernel expressions. Every node caches its hash, its size, the range of its loose bound variables, and whether
-- it mentions a free variable or a universe parameter. Equality ignores binder names and binder annotations, as
-- the kernel does. See docs/design.md for why terms are not hash-consed.
module Tenet.Expr
  ( Expr, Info (..), BinderInfo (..), Literal (..), FVarId
  , pattern BVar, pattern FVar, pattern Sort, pattern Const, pattern App
  , pattern Lam, pattern Pi, pattern Let, pattern Lit, pattern Proj
  , exprHash, exprSize, looseBVarRange, hasLooseBVars, hasFVar, hasLevelParam
  , ptrEq
  , mkApp, mkAppList, mkRevApp, getAppFn, getAppArgs, getAppRevArgs, getAppNumArgs
  , isConstOf, isAppOfArity, mkArrow, mkProp, mkNatLit, mkStrLit, mkConstE
  , isNatLit, isStrLit, isBVarOf, isBinding
  , showExpr
  ) where

import Data.Bits (bit, shiftL, shiftR, testBit, xor, (.&.), (.|.))
import qualified Data.Text as T
import Control.Monad (when)
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Tenet.HTable
import Tenet.Level
import Tenet.Name

type FVarId = Int

data BinderInfo = BDefault | BImplicit | BStrictImplicit | BInstImplicit
  deriving (Eq, Show)

data Literal = NatLit !Integer | StrLit !T.Text
  deriving (Eq, Show)

-- | Facts cached on every node, in two words: the structural hash, and one word packing the range of loose
-- bound variables (24 bits), whether the term mentions a free variable and a universe parameter (2 bits), and its
-- node count, saturating (the rest). Three separate fields cost five words and an indirection on every node,
-- which was most of the memory of a large export.
data Info = Info
  { iHash :: {-# UNPACK #-} !Int
  , iMeta :: {-# UNPACK #-} !Int
  }

iLBR :: Info -> Int
iLBR i = iMeta i .&. 0xFFFFFF
{-# INLINE iLBR #-}

iFV :: Info -> Bool
iFV i = testBit (iMeta i) 24
{-# INLINE iFV #-}

iLP :: Info -> Bool
iLP i = testBit (iMeta i) 25
{-# INLINE iLP #-}

iSz :: Info -> Int
iSz i = iMeta i `shiftR` 26
{-# INLINE iSz #-}

mkMeta :: Int -> Bool -> Bool -> Int -> Int
mkMeta lbr fv lp sz =
  (min lbr 0xFFFFFF) .|. (if fv then bit 24 else 0) .|. (if lp then bit 25 else 0) .|. (min sz 0x3FFFFFFF `shiftL` 26)
{-# INLINE mkMeta #-}

data Expr
  = EBVar {-# UNPACK #-} !Info !Int
  | EFVar {-# UNPACK #-} !Info !FVarId
  | ESort {-# UNPACK #-} !Info !Level
  | EConst {-# UNPACK #-} !Info !Name [Level]
  | EApp {-# UNPACK #-} !Info !Expr !Expr
  | ELam {-# UNPACK #-} !Info !Name !BinderInfo !Expr !Expr
  | EPi {-# UNPACK #-} !Info !Name !BinderInfo !Expr !Expr
  | ELet {-# UNPACK #-} !Info !Name !Expr !Expr !Expr
  | ELit {-# UNPACK #-} !Info !Literal
  | EProj {-# UNPACK #-} !Info !Name !Int !Expr

infoOf :: Expr -> Info
infoOf = \case
  EBVar i _ -> i
  EFVar i _ -> i
  ESort i _ -> i
  EConst i _ _ -> i
  EApp i _ _ -> i
  ELam i _ _ _ _ -> i
  EPi i _ _ _ _ -> i
  ELet i _ _ _ _ -> i
  ELit i _ -> i
  EProj i _ _ _ -> i
{-# INLINE infoOf #-}

exprHash :: Expr -> Int
exprHash = iHash . infoOf

exprSize :: Expr -> Int
exprSize = iSz . infoOf

looseBVarRange :: Expr -> Int
looseBVarRange = iLBR . infoOf

hasLooseBVars :: Expr -> Bool
hasLooseBVars e = looseBVarRange e > 0

hasFVar :: Expr -> Bool
hasFVar = iFV . infoOf

hasLevelParam :: Expr -> Bool
hasLevelParam = iLP . infoOf

-- ---------------------------------------------------------------- smart constructors

-- | Saturating size addition (plus the node itself).
addSz :: Int -> Int -> Int
addSz a b = let s = a + b + 1 in if s < 0 || s > 1000000000 then 1000000000 else s

mixH :: Int -> Int -> Int
mixH a b = ((a `shiftL` 5) + a + (a `shiftR` 2)) `xor` (b * 0x1e3779b97f4a7c15)

mkBVar :: Int -> Expr
mkBVar i = EBVar (Info (mixH 11 i) (mkMeta (i + 1) False False 1)) i

mkFVar :: FVarId -> Expr
mkFVar i = EFVar (Info (mixH 13 i) (mkMeta 0 True False 1)) i

mkSort :: Level -> Expr
mkSort l = ESort (Info (mixH 17 (levelHash l)) (mkMeta 0 False (levelHasParam l) 1)) l

mkConstE :: Name -> [Level] -> Expr
mkConstE n ls =
  EConst (Info (foldl (\h l -> mixH h (levelHash l)) (mixH 19 (nameHash n)) ls) (mkMeta 0 False (any levelHasParam ls) 1)) n ls

mkAppE :: Expr -> Expr -> Expr
mkAppE f a =
  let fi = infoOf f
      ai = infoOf a
  in EApp (Info (mixH (mixH 23 (iHash fi)) (iHash ai))
                (mkMeta (max (iLBR fi) (iLBR ai)) (iFV fi || iFV ai) (iLP fi || iLP ai) (addSz (iSz fi) (iSz ai)))) f a

binderInfo4 :: Int -> Expr -> Expr -> Info
binderInfo4 tag d b =
  let di = infoOf d
      bi = infoOf b
  in Info (mixH (mixH tag (iHash di)) (iHash bi))
          (mkMeta (max (iLBR di) (iLBR bi - 1)) (iFV di || iFV bi) (iLP di || iLP bi) (addSz (iSz di) (iSz bi)))

mkLam :: Name -> BinderInfo -> Expr -> Expr -> Expr
mkLam n bi d b = ELam (binderInfo4 29 d b) n bi d b

mkPi :: Name -> BinderInfo -> Expr -> Expr -> Expr
mkPi n bi d b = EPi (binderInfo4 31 d b) n bi d b

mkLet :: Name -> Expr -> Expr -> Expr -> Expr
mkLet n t v b =
  let ti = infoOf t
      vi = infoOf v
      bi = infoOf b
  in ELet (Info (mixH (mixH (mixH 37 (iHash ti)) (iHash vi)) (iHash bi))
                (mkMeta (max (max (iLBR ti) (iLBR vi)) (iLBR bi - 1))
                        (iFV ti || iFV vi || iFV bi) (iLP ti || iLP vi || iLP bi)
                        (addSz (iSz ti) (addSz (iSz vi) (iSz bi))))) n t v b

mkLit :: Literal -> Expr
mkLit l = ELit (Info (mixH 41 (case l of NatLit n -> fromInteger n; StrLit s -> T.length s * 7 + T.foldl' (\h c -> h * 31 + fromEnum c) 5 s)) (mkMeta 0 False False 1)) l

mkProj :: Name -> Int -> Expr -> Expr
mkProj n i s =
  let si = infoOf s
  in EProj (Info (mixH (mixH (mixH 43 (nameHash n)) i) (iHash si)) (mkMeta (iLBR si) (iFV si) (iLP si) (addSz 1 (iSz si)))) n i s

pattern BVar :: Int -> Expr
pattern BVar i <- EBVar _ i where BVar i = mkBVar i

pattern FVar :: FVarId -> Expr
pattern FVar i <- EFVar _ i where FVar i = mkFVar i

pattern Sort :: Level -> Expr
pattern Sort l <- ESort _ l where Sort l = mkSort l

pattern Const :: Name -> [Level] -> Expr
pattern Const n ls <- EConst _ n ls where Const n ls = mkConstE n ls

pattern App :: Expr -> Expr -> Expr
pattern App f a <- EApp _ f a where App f a = mkAppE f a

pattern Lam :: Name -> BinderInfo -> Expr -> Expr -> Expr
pattern Lam n bi d b <- ELam _ n bi d b where Lam n bi d b = mkLam n bi d b

pattern Pi :: Name -> BinderInfo -> Expr -> Expr -> Expr
pattern Pi n bi d b <- EPi _ n bi d b where Pi n bi d b = mkPi n bi d b

pattern Let :: Name -> Expr -> Expr -> Expr -> Expr
pattern Let n t v b <- ELet _ n t v b where Let n t v b = mkLet n t v b

pattern Lit :: Literal -> Expr
pattern Lit l <- ELit _ l where Lit l = mkLit l

pattern Proj :: Name -> Int -> Expr -> Expr
pattern Proj n i s <- EProj _ n i s where Proj n i s = mkProj n i s

{-# COMPLETE BVar, FVar, Sort, Const, App, Lam, Pi, Let, Lit, Proj #-}

-- ---------------------------------------------------------------- equality

-- | Structural equality ignoring binder names and annotations. Large terms in this kernel are shared DAGs, and
-- comparing two equal copies node by node is exponential in the depth of the sharing, so big pairs that are
-- not pointer-equal are compared with a table of the pairs already visited, as Lean's @expr_eq_fn@ does: a
-- revisited pair is assumed equal, which is sound because any inequality aborts the whole comparison.
instance Eq Expr where
  a == b
    | ptrEq a b = True
    | iHash (infoOf a) /= iHash (infoOf b) = False
    | iSz (infoOf a) <= eqMemoThreshold = eqSmall a b
    | otherwise = unsafeDupablePerformIO (do t <- newHTable; eqMemo t a b)

eqMemoThreshold :: Int
eqMemoThreshold = 64

eqSmall :: Expr -> Expr -> Bool
eqSmall x y
  | ptrEq x y = True
  | iHash (infoOf x) /= iHash (infoOf y) = False
  | otherwise = case (x, y) of
      (EBVar _ i, EBVar _ j) -> i == j
      (EFVar _ i, EFVar _ j) -> i == j
      (ESort _ l, ESort _ m) -> l == m
      (EConst _ n ls, EConst _ m ms) -> n == m && ls == ms
      (EApp _ f a, EApp _ g b) -> eqSmall a b && eqSmall f g
      (ELam _ _ _ d a, ELam _ _ _ e b) -> eqSmall d e && eqSmall a b
      (EPi _ _ _ d a, EPi _ _ _ e b) -> eqSmall d e && eqSmall a b
      (ELet _ _ t v a, ELet _ _ u w b) -> eqSmall t u && eqSmall v w && eqSmall a b
      (ELit _ l, ELit _ m) -> l == m
      (EProj _ n i a, EProj _ m j b) -> i == j && n == m && eqSmall a b
      _ -> False

eqMemo :: HTable (Expr, Expr) -> Expr -> Expr -> IO Bool
eqMemo t x y
  | ptrEq x y = pure True
  | iHash (infoOf x) /= iHash (infoOf y) = pure False
  | iSz (infoOf x) <= eqMemoThreshold = pure (eqSmall x y)
  | otherwise = do
      let h = iHash (infoOf x)
      seen <- lookupBy t h (\(u, v) -> ptrEq u x && ptrEq v y)
      case seen of
        Just _ -> pure True
        Nothing -> do
          r <- case (x, y) of
            (EApp _ f a, EApp _ g b) -> both (eqMemo t a b) (eqMemo t f g)
            (ELam _ _ _ d a, ELam _ _ _ e b) -> both (eqMemo t d e) (eqMemo t a b)
            (EPi _ _ _ d a, EPi _ _ _ e b) -> both (eqMemo t d e) (eqMemo t a b)
            (ELet _ _ ty v a, ELet _ _ ty' w b) -> both (eqMemo t ty ty') (both (eqMemo t v w) (eqMemo t a b))
            (EProj _ n i a, EProj _ m j b) -> if i == j && n == m then eqMemo t a b else pure False
            _ -> pure False
          when r $ insertH t h (x, y)
          pure r
  where
    both p q = p >>= \ok -> if ok then q else pure False

ptrEq :: a -> a -> Bool
ptrEq a b = isTrue# (reallyUnsafePtrEquality# a b)
{-# INLINE ptrEq #-}

-- ---------------------------------------------------------------- application spines

mkApp :: Expr -> [Expr] -> Expr
mkApp = foldl App

mkAppList :: Expr -> [Expr] -> Expr
mkAppList = mkApp

-- | Apply to arguments given in reverse order (last argument first).
mkRevApp :: Expr -> [Expr] -> Expr
mkRevApp f revArgs = foldr (flip App) f revArgs

getAppFn :: Expr -> Expr
getAppFn (App f _) = getAppFn f
getAppFn e = e

getAppArgs :: Expr -> [Expr]
getAppArgs = go []
  where
    go acc (App f a) = go (a : acc) f
    go acc _ = acc

-- | Arguments, last first.
getAppRevArgs :: Expr -> [Expr]
getAppRevArgs (App f a) = a : getAppRevArgs f
getAppRevArgs _ = []

getAppNumArgs :: Expr -> Int
getAppNumArgs (App f _) = 1 + getAppNumArgs f
getAppNumArgs _ = 0

isConstOf :: Expr -> Name -> Bool
isConstOf (Const n _) m = n == m
isConstOf _ _ = False

isAppOfArity :: Expr -> Name -> Int -> Bool
isAppOfArity e n k = getAppNumArgs e == k && isConstOf (getAppFn e) n

mkArrow :: Expr -> Expr -> Expr
mkArrow d b = Pi (nameStr "a") BDefault d b

mkProp :: Expr
mkProp = Sort LZero

mkNatLit :: Integer -> Expr
mkNatLit = Lit . NatLit

mkStrLit :: T.Text -> Expr
mkStrLit = Lit . StrLit

isNatLit :: Expr -> Bool
isNatLit (Lit (NatLit _)) = True
isNatLit _ = False

isStrLit :: Expr -> Bool
isStrLit (Lit (StrLit _)) = True
isStrLit _ = False

isBVarOf :: Expr -> Int -> Bool
isBVarOf (BVar i) j = i == j
isBVarOf _ _ = False

isBinding :: Expr -> Bool
isBinding = \case
  Lam {} -> True
  Pi {} -> True
  _ -> False

-- ---------------------------------------------------------------- printing

showExpr :: Expr -> String
showExpr = go (0 :: Int)
  where
    go d e = case e of
      BVar i -> "#" ++ show i
      FVar i -> "_fv" ++ show i
      Sort l -> if l == LZero then "Prop" else if l == lOne then "Type" else "Sort " ++ paren (showLevel l)
      Const n ls -> showName n ++ (if null ls then "" else ".{" ++ commas (map showLevel ls) ++ "}")
      App {} -> par (d > 1) (unwords (map (go 2) (getAppFn e : getAppArgs e)))
      Lam n _ t b -> par (d > 0) ("fun (" ++ showName n ++ " : " ++ go 0 t ++ ") => " ++ go 0 b)
      Pi n _ t b -> par (d > 0) ("(" ++ showName n ++ " : " ++ go 0 t ++ ") -> " ++ go 0 b)
      Let n t v b -> par (d > 0) ("let " ++ showName n ++ " : " ++ go 0 t ++ " := " ++ go 0 v ++ "; " ++ go 0 b)
      Lit (NatLit n) -> show n
      Lit (StrLit s) -> show (T.unpack s)
      Proj n i s -> go 2 s ++ "." ++ showName n ++ "#" ++ show i
    par c s = if c then "(" ++ s ++ ")" else s
    paren s = "(" ++ s ++ ")"
    commas [] = ""
    commas [x] = x
    commas (x : xs) = x ++ ", " ++ commas xs

instance Show Expr where
  show = showExpr
