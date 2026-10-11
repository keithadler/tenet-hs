{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Quotient types: the four built-in constants and their fixed types.
module Tenet.Quot (addQuot, isQuotDecl) where

import Control.Monad (unless, when)
import Tenet.Env
import Tenet.Expr
import Tenet.Level
import Tenet.Name
import Tenet.TypeChecker

nQuot, nQuotMk, nQuotLift, nQuotInd, nEq :: Name
nQuot = nameOf ["Quot"]
nQuotMk = nameOf ["Quot", "mk"]
nQuotLift = nameOf ["Quot", "lift"]
nQuotInd = nameOf ["Quot", "ind"]
nEq = nameOf ["Eq"]

isQuotDecl :: Name -> Bool
isQuotDecl n = n `elem` [nQuot, nQuotMk, nQuotLift, nQuotInd]

-- | The environment must already contain @Eq@ with exactly the expected shape.
checkEqType :: Env -> TC -> IO ()
checkEqType env tc = do
  let bad = kerr
  meq <- findConst env nEq
  eqInfo <- maybe (bad "failed to initialize quot module, environment does not have 'Eq' type") pure meq
  ctors <- case ciKind eqInfo of
    KInduct { kCtors = cs } -> pure cs
    _ -> bad "failed to initialize quot module, environment does not have 'Eq' type"
  when (length (ciLParams eqInfo) /= 1) $ bad "failed to initialize quot module, unexpected number of universe params at 'Eq' type"
  refl <- case ctors of
    [c] -> getConst env c
    _ -> bad "failed to initialize quot module, unexpected number of constructors for 'Eq' type"
  u <- case ciLParams eqInfo of
    [p] -> pure (LParam p)
    _ -> bad "failed to initialize quot module, unexpected number of universe params at 'Eq' type"
  alpha <- mkLocalDecl tc (nameStr "α") (Sort u) BImplicit
  expectedEq <- mkPiFVars tc [alpha] (mkArrow alpha (mkArrow alpha mkProp))
  unless (expectedEq == ciType eqInfo) $ bad "failed to initialize quot module, 'Eq' has an unexpected type"
  when (length (ciLParams refl) /= 1) $ bad "failed to initialize quot module, unexpected type for 'Eq' type constructor"
  u' <- case ciLParams refl of
    [p] -> pure (LParam p)
    _ -> bad "failed to initialize quot module, unexpected type for 'Eq' type constructor"
  alpha' <- mkLocalDecl tc (nameStr "α") (Sort u') BImplicit
  a <- mkLocalDecl tc (nameStr "a") alpha' BDefault
  expectedRefl <- mkPiFVars tc [alpha', a] (mkApp (Const nEq [u']) [alpha', a, a])
  unless (expectedRefl == ciType refl) $ bad "failed to initialize quot module, unexpected type for 'Eq' type constructor"

-- | Add @Quot@, @Quot.mk@, @Quot.lift@ and @Quot.ind@ with their fixed types.
addQuot :: Env -> IO ()
addQuot env = do
  already <- quotInitialized env
  unless already $ do
    tc <- newTC env Safe
    checkEqType env tc
    mapM_ (checkName env) [nQuot, nQuotMk, nQuotLift, nQuotInd]
    let uN = nameStr "u"
        vN = nameStr "v"
        u = LParam uN
        v = LParam vN
        sortU = Sort u
        sortV = Sort v
        add n lps ty k = addCore env (ConstantInfo n lps ty (KQuot k))
    -- Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
    alpha <- mkLocalDecl tc (nameStr "α") sortU BImplicit
    r <- mkLocalDecl tc (nameStr "r") (mkArrow alpha (mkArrow alpha mkProp)) BDefault
    ty1 <- mkPiFVars tc [alpha, r] sortU
    add nQuot [uN] ty1 QType
    let quotR = mkApp (Const nQuot [u]) [alpha, r]
    a <- mkLocalDecl tc (nameStr "a") alpha BDefault
    -- Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot r
    ty2 <- mkPiFVars tc [alpha, r, a] quotR
    add nQuotMk [uN] ty2 QCtor
    -- r becomes implicit for lift and ind
    alpha2 <- mkLocalDecl tc (nameStr "α") sortU BImplicit
    r2 <- mkLocalDecl tc (nameStr "r") (mkArrow alpha2 (mkArrow alpha2 mkProp)) BImplicit
    let quotR2 = mkApp (Const nQuot [u]) [alpha2, r2]
    a2 <- mkLocalDecl tc (nameStr "a") alpha2 BDefault
    beta <- mkLocalDecl tc (nameStr "β") sortV BImplicit
    f <- mkLocalDecl tc (nameStr "f") (mkArrow alpha2 beta) BDefault
    b <- mkLocalDecl tc (nameStr "b") alpha2 BDefault
    let rab = mkApp r2 [a2, b]
        faEqFb = mkApp (Const nEq [v]) [beta, App f a2, App f b]
    sanity <- mkPiFVars tc [a2, b] (mkArrow rab faEqFb)
    -- Quot.lift.{u v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) : (∀ a b, r a b → f a = f b) → Quot r → β
    ty3 <- mkPiFVars tc [alpha2, r2, beta, f] (mkArrow sanity (mkArrow quotR2 beta))
    add nQuotLift [uN, vN] ty3 QLift
    -- {β : Quot r → Prop}
    beta2 <- mkLocalDecl tc (nameStr "β") (mkArrow quotR2 mkProp) BImplicit
    let quotMkA = mkApp (Const nQuotMk [u]) [alpha2, r2, a2]
    allQuot <- mkPiFVars tc [a2] (App beta2 quotMkA)
    q <- mkLocalDecl tc (nameStr "q") quotR2 BDefault
    inner <- mkPiFVars tc [q] (App beta2 q)
    -- Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} : (∀ a, β (Quot.mk r a)) → ∀ q, β q
    ty4 <- mkPiFVars tc [alpha2, r2, beta2] (Pi (nameStr "mk") BDefault allQuot inner)
    add nQuotInd [uN] ty4 QInd
    markQuotInitialized env
