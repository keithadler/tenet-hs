{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
{-# LANGUAGE MagicHash #-}
-- | Kernel expressions. Every node caches its hash, the range of its loose bound variables, and whether it
-- mentions a free variable or a universe parameter. Equality ignores binder names and binder annotations,
-- as the kernel does.
module Tenet.Expr
  ( Expr, Info (..), BinderInfo (..), Literal (..), FVarId
  , pattern BVar, pattern FVar, pattern Sort, pattern Const, pattern App
  , pattern Lam, pattern Pi, pattern Let, pattern Lit, pattern Proj
  , exprHash, looseBVarRange, hasLooseBVars, hasFVar, hasLevelParam
  , eqExprStrict, ptrEq
  , mkApp, mkAppList, mkRevApp, getAppFn, getAppArgs, getAppRevArgs, getAppNumArgs
  , isConstOf, isAppOfArity, mkArrow, mkProp, mkNatLit, mkStrLit, mkConstE
  , isNatLit, isStrLit, isBVarOf, isBinding
  , showExpr
  ) where

import Data.Bits (xor, shiftL, shiftR)
import qualified Data.Text as T
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)
import Tenet.Level
import Tenet.Name

type FVarId = Int

data BinderInfo = BDefault | BImplicit | BStrictImplicit | BInstImplicit
  deriving (Eq, Show)

data Literal = NatLit !Integer | StrLit !T.Text
  deriving (Eq, Show)

data Info = Info
  { iHash :: {-# UNPACK #-} !Int
  , iLBR :: {-# UNPACK #-} !Int   -- ^ loose bound variable range
  , iFV :: !Bool                  -- ^ mentions a free variable
  , iLP :: !Bool                  -- ^ mentions a universe parameter
  }

data Expr
  = EBVar !Info !Int
  | EFVar !Info !FVarId
  | ESort !Info !Level
  | EConst !Info !Name [Level]
  | EApp !Info !Expr !Expr
  | ELam !Info !Name !BinderInfo !Expr !Expr
  | EPi !Info !Name !BinderInfo !Expr !Expr
  | ELet !Info !Name !Expr !Expr !Expr
  | ELit !Info !Literal
  | EProj !Info !Name !Int !Expr

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

looseBVarRange :: Expr -> Int
looseBVarRange = iLBR . infoOf

hasLooseBVars :: Expr -> Bool
hasLooseBVars e = looseBVarRange e > 0

hasFVar :: Expr -> Bool
hasFVar = iFV . infoOf

hasLevelParam :: Expr -> Bool
hasLevelParam = iLP . infoOf

mixH :: Int -> Int -> Int
mixH a b = ((a `shiftL` 5) + a + (a `shiftR` 2)) `xor` (b * 0x1e3779b97f4a7c15)

-- ---------------------------------------------------------------- smart constructors

mkBVar :: Int -> Expr
mkBVar i = EBVar (Info (mixH 11 i) (i + 1) False False) i

mkFVar :: FVarId -> Expr
mkFVar i = EFVar (Info (mixH 13 i) 0 True False) i

mkSort :: Level -> Expr
mkSort l = ESort (Info (mixH 17 (levelHash l)) 0 False (levelHasParam l)) l

mkConstE :: Name -> [Level] -> Expr
mkConstE n ls =
  EConst (Info (foldl (\h l -> mixH h (levelHash l)) (mixH 19 (nameHash n)) ls) 0 False (any levelHasParam ls)) n ls

mkAppE :: Expr -> Expr -> Expr
mkAppE f a =
  let fi = infoOf f
      ai = infoOf a
  in EApp (Info (mixH (mixH 23 (iHash fi)) (iHash ai)) (max (iLBR fi) (iLBR ai)) (iFV fi || iFV ai) (iLP fi || iLP ai)) f a

binderInfo4 :: Int -> Expr -> Expr -> Info
binderInfo4 tag d b =
  let di = infoOf d
      bi = infoOf b
  in Info (mixH (mixH tag (iHash di)) (iHash bi)) (max (iLBR di) (iLBR bi - 1)) (iFV di || iFV bi) (iLP di || iLP bi)

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
                (max (max (iLBR ti) (iLBR vi)) (iLBR bi - 1))
                (iFV ti || iFV vi || iFV bi) (iLP ti || iLP vi || iLP bi)) n t v b

mkLit :: Literal -> Expr
mkLit l = ELit (Info (mixH 41 (case l of NatLit n -> fromInteger n; StrLit s -> T.length s * 7 + T.foldl' (\h c -> h * 31 + fromEnum c) 5 s)) 0 False False) l

mkProj :: Name -> Int -> Expr -> Expr
mkProj n i s =
  let si = infoOf s
  in EProj (Info (mixH (mixH (mixH 43 (nameHash n)) i) (iHash si)) (iLBR si) (iFV si) (iLP si)) n i s

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

ptrEq :: a -> a -> Bool
ptrEq a b = isTrue# (reallyUnsafePtrEquality# a b)
{-# INLINE ptrEq #-}

-- | Structural equality ignoring binder names and annotations.
instance Eq Expr where
  a == b
    | ptrEq a b = True
    | exprHash a /= exprHash b = False
    | otherwise = go a b
    where
      go x y | ptrEq x y = True
      go (EBVar _ i) (EBVar _ j) = i == j
      go (EFVar _ i) (EFVar _ j) = i == j
      go (ESort _ l) (ESort _ m) = l == m
      go (EConst _ n ls) (EConst _ m ms) = n == m && ls == ms
      go (EApp _ f x) (EApp _ g y) = x == y && f == g
      go (ELam _ _ _ d x) (ELam _ _ _ e y) = d == e && x == y
      go (EPi _ _ _ d x) (EPi _ _ _ e y) = d == e && x == y
      go (ELet _ _ t v x) (ELet _ _ u w y) = t == u && v == w && x == y
      go (ELit _ l) (ELit _ m) = l == m
      go (EProj _ n i x) (EProj _ m j y) = i == j && n == m && x == y
      go _ _ = False

-- | Equality that also compares binder names and annotations.
eqExprStrict :: Expr -> Expr -> Bool
eqExprStrict a b
  | ptrEq a b = True
  | exprHash a /= exprHash b = False
  | otherwise = case (a, b) of
      (App f x, App g y) -> eqExprStrict x y && eqExprStrict f g
      (Lam n bi d x, Lam m bj e y) -> n == m && bi == bj && eqExprStrict d e && eqExprStrict x y
      (Pi n bi d x, Pi m bj e y) -> n == m && bi == bj && eqExprStrict d e && eqExprStrict x y
      (Let n t v x, Let m u w y) -> n == m && eqExprStrict t u && eqExprStrict v w && eqExprStrict x y
      (Proj n i x, Proj m j y) -> n == m && i == j && eqExprStrict x y
      _ -> a == b

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
