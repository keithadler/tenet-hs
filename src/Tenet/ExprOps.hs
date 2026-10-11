{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Traversals and substitutions on expressions.
module Tenet.ExprOps
  ( replaceE, replaceIO, findE, forEachE, forEachIO
  , hasLooseBVar, liftLooseBVars, lowerLooseBVars
  , instantiate, instantiate1, instantiateRev, abstractFVars
  , instantiateLevelParams
  , headBetaReduce, cheapBetaReduce, betaRev
  , consumeTypeAnnotations, inferImplicit
  , updateLam, updatePi
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Control.Monad (when)
import Data.IORef
import Tenet.Expr
import Tenet.Level
import Tenet.Name

-- | Memoized rebuild. The callback receives each subterm and the number of binders above it; a 'Just'
-- replaces the subterm without descending. Results for shared subterms are cached by (hash, offset).
replaceE :: (Expr -> Int -> Maybe Expr) -> Expr -> Expr
replaceE f e0 = fst (go 0 e0 IM.empty)
  where
    go :: Int -> Expr -> IM.IntMap [(Expr, Int, Expr)] -> (Expr, IM.IntMap [(Expr, Int, Expr)])
    go !off t !cache = case f t off of
      Just r -> (r, cache)
      Nothing -> case t of
        App {} -> memo off t cache (step off t)
        Lam {} -> memo off t cache (step off t)
        Pi {} -> memo off t cache (step off t)
        Let {} -> memo off t cache (step off t)
        Proj {} -> memo off t cache (step off t)
        _ -> (t, cache)
    memo off t cache k =
      let key = exprHash t * 31 + off
      in case IM.lookup key cache of
           Just bucket | Just r <- lookupB t off bucket -> (r, cache)
           _ -> let (r, cache') = k cache
                in (r, IM.insertWith (++) key [(t, off, r)] cache')
    lookupB _ _ [] = Nothing
    lookupB t off ((u, o, r) : rest)
      | o == off && u == t = Just r
      | otherwise = lookupB t off rest
    step off t cache = case t of
      App fn a ->
        let (fn', c1) = go off fn cache
            (a', c2) = go off a c1
        in (if ptrEq fn fn' && ptrEq a a' then t else App fn' a', c2)
      Lam n bi d b ->
        let (d', c1) = go off d cache
            (b', c2) = go (off + 1) b c1
        in (if ptrEq d d' && ptrEq b b' then t else Lam n bi d' b', c2)
      Pi n bi d b ->
        let (d', c1) = go off d cache
            (b', c2) = go (off + 1) b c1
        in (if ptrEq d d' && ptrEq b b' then t else Pi n bi d' b', c2)
      Let n ty v b ->
        let (ty', c1) = go off ty cache
            (v', c2) = go off v c1
            (b', c3) = go (off + 1) b c2
        in (if ptrEq ty ty' && ptrEq v v' && ptrEq b b' then t else Let n ty' v' b', c3)
      Proj n i s ->
        let (s', c1) = go off s cache
        in (if ptrEq s s' then t else Proj n i s', c1)
      _ -> (t, cache)

updateLam :: Expr -> Expr -> Expr -> Expr
updateLam (Lam n bi _ _) d b = Lam n bi d b
updateLam e _ _ = e

updatePi :: Expr -> Expr -> Expr -> Expr
updatePi (Pi n bi _ _) d b = Pi n bi d b
updatePi e _ _ = e

-- | Visit every subterm (shared ones once); the predicate returns False to skip a subterm's children.
forEachE :: (Expr -> Int -> Bool) -> Expr -> ()
forEachE f e0 = go 0 e0 IS.empty `seq` ()
  where
    go !off t seen
      | compound t, let k = exprHash t * 31 + off, IS.member k seen = seen
      | not (f t off) = seen
      | otherwise =
          let seen1 = if compound t then IS.insert (exprHash t * 31 + off) seen else seen
          in case t of
               App fn a -> go off a (go off fn seen1)
               Lam _ _ d b -> go (off + 1) b (go off d seen1)
               Pi _ _ d b -> go (off + 1) b (go off d seen1)
               Let _ ty v b -> go (off + 1) b (go off v (go off ty seen1))
               Proj _ _ s -> go off s seen1
               _ -> seen1
    compound = \case
      App {} -> True
      Lam {} -> True
      Pi {} -> True
      Let {} -> True
      Proj {} -> True
      _ -> False

-- | Does some subterm satisfy the predicate?
findE :: (Expr -> Int -> Bool) -> Expr -> Bool
findE p e0 = go 0 e0
  where
    go !off t
      | p t off = True
      | otherwise = case t of
          App fn a -> go off fn || go off a
          Lam _ _ d b -> go off d || go (off + 1) b
          Pi _ _ d b -> go off d || go (off + 1) b
          Let _ ty v b -> go off ty || go off v || go (off + 1) b
          Proj _ _ s -> go off s
          _ -> False

hasLooseBVar :: Expr -> Int -> Bool
hasLooseBVar e i
  | i >= looseBVarRange e = False
  | otherwise = go 0 e
  where
    go !off t
      | i + off >= looseBVarRange t = False
      | otherwise = case t of
          BVar j -> j == i + off
          App fn a -> go off fn || go off a
          Lam _ _ d b -> go off d || go (off + 1) b
          Pi _ _ d b -> go off d || go (off + 1) b
          Let _ ty v b -> go off ty || go off v || go (off + 1) b
          Proj _ _ s -> go off s
          _ -> False

-- | Add @d@ to every loose bound variable with index at least @s@.
liftLooseBVars :: Expr -> Int -> Int -> Expr
liftLooseBVars e s d
  | d == 0 || s >= looseBVarRange e = e
  | otherwise = replaceE f e
  where
    f t off
      | s + off >= looseBVarRange t = Just t
      | BVar i <- t, i >= s + off = Just (BVar (i + d))
      | otherwise = Nothing

-- | Subtract @d@ from every loose bound variable with index at least @s@.
lowerLooseBVars :: Expr -> Int -> Int -> Expr
lowerLooseBVars e s d
  | d == 0 || s >= looseBVarRange e = e
  | otherwise = replaceE f e
  where
    f t off
      | s + off >= looseBVarRange t = Just t
      | BVar i <- t, i >= s + off = Just (BVar (i - d))
      | otherwise = Nothing

-- | Replace loose bound variables @s .. s+n-1@ by @subst !! 0 .. subst !! (n-1)@; higher ones are lowered by @n@.
instantiate :: Expr -> Int -> [Expr] -> Expr
instantiate e s subst
  | s >= looseBVarRange e || n == 0 = e
  | otherwise = replaceE f e
  where
    n = length subst
    arr = IM.fromList (zip [0 ..] subst)
    f m off
      | s1 >= looseBVarRange m = Just m
      | BVar i <- m, i >= s1 =
          if i < s1 + n then Just (liftLooseBVars (arr IM.! (i - s1)) 0 off) else Just (BVar (i - n))
      | otherwise = Nothing
      where s1 = s + off

instantiate1 :: Expr -> Expr -> Expr
instantiate1 e v
  | not (hasLooseBVars e) = e
  | otherwise = instantiate e 0 [v]

-- | Instantiate with the substitution reversed: variable @i@ gets @subst !! (n-1-i)@.
instantiateRev :: Expr -> [Expr] -> Expr
instantiateRev e subst
  | not (hasLooseBVars e) || n == 0 = e
  | otherwise = replaceE f e
  where
    n = length subst
    arr = IM.fromList (zip [0 ..] subst)
    f m off
      | off >= looseBVarRange m = Just m
      | BVar i <- m, i >= off =
          if i < off + n then Just (liftLooseBVars (arr IM.! (n - (i - off) - 1)) 0 off) else Just (BVar (i - n))
      | otherwise = Nothing

-- | Replace the free variables by bound variables: @fvars !! i@ becomes @#(n-1-i)@ at the top level.
abstractFVars :: Expr -> [FVarId] -> Expr
abstractFVars e fvs
  | not (hasFVar e) || n == 0 = e
  | otherwise = replaceE f e
  where
    n = length fvs
    pos = IM.fromList (zip fvs [0 ..])
    f m off
      | not (hasFVar m) = Just m
      | FVar i <- m = case IM.lookup i pos of
          Just k -> Just (BVar (off + n - k - 1))
          Nothing -> Nothing
      | otherwise = Nothing

instantiateLevelParams :: Expr -> [Name] -> [Level] -> Expr
instantiateLevelParams e ps ls
  | not (hasLevelParam e) || null ps = e
  | otherwise = replaceE f e
  where
    f t _
      | not (hasLevelParam t) = Just t
      | otherwise = case t of
          Const c us -> Just (Const c (map (instantiateLevel ps ls) us))
          Sort l -> Just (Sort (instantiateLevel ps ls l))
          _ -> Nothing

-- | Apply a lambda to reversed arguments (@f a1 .. an@ is given as @[an .. a1]@), consuming as many binders as possible.
betaRev :: Expr -> [Expr] -> Expr
betaRev f revArgs =
  let n = length revArgs
      peel (Lam _ _ _ b) k | k < n = peel b (k + 1)
      peel b k = (b, k)
      (body, m) = peel f 0
      consumed = drop (n - m) revArgs   -- [am .. a1]: variable 0 is the innermost binder, which takes am
  in mkRevApp (instantiate body 0 consumed) (take (n - m) revArgs)

-- | Beta-reduce the head of an application repeatedly.
headBetaReduce :: Expr -> Expr
headBetaReduce e = case e of
  App {} | Lam {} <- getAppFn e -> headBetaReduce (betaRev (getAppFn e) (getAppRevArgs e))
  _ -> e

-- | The kernel's @cheap_beta_reduce@: beta-reduce only when the result needs no substitution.
cheapBetaReduce :: Expr -> Expr
cheapBetaReduce e = case e of
  App {} | Lam {} <- getAppFn e ->
    let args = getAppArgs e
        n = length args
        peel (Lam _ _ _ b) i | i < n = peel b (i + 1)
        peel x i = (x, i)
        (fn, k) = peel (getAppFn e) 0
    in if | not (hasLooseBVars fn) -> mkApp fn (drop k args)
          | BVar b <- fn -> mkApp (args !! (k - b - 1)) (drop k args)
          | otherwise -> e
  _ -> e

consumeTypeAnnotations :: Expr -> Expr
consumeTypeAnnotations e
  | isAppOfArity e (nameStr "optParam") 2 || isAppOfArity e (nameStr "autoParam") 2 =
      case e of App (App _ a) _ -> consumeTypeAnnotations a; _ -> e
  | isAppOfArity e (nameStr "outParam") 1 || isAppOfArity e (nameStr "semiOutParam") 1 =
      case e of App _ a -> consumeTypeAnnotations a; _ -> e
  | otherwise = e

-- | Mark as implicit those Pi binders that can be inferred from later explicit binders (@infer_implicit@).
inferImplicit :: Expr -> Int -> Bool -> Expr
inferImplicit t numParams strict
  | numParams == 0 = t
  | Pi n bi d b <- t =
      let nb = inferImplicit b (numParams - 1) strict
      in if | bi /= BDefault -> Pi n bi d nb
            | hasLooseBVarsInDomain nb 0 strict -> Pi n BImplicit d nb
            | otherwise -> Pi n bi d nb
  | otherwise = t

hasLooseBVarsInDomain :: Expr -> Int -> Bool -> Bool
hasLooseBVarsInDomain b vidx strict = case b of
  Pi _ bi d body
    | hasLooseBVar d vidx && (bi == BDefault || hasLooseBVarsInDomain body 0 strict) -> True
    | otherwise -> hasLooseBVarsInDomain body (vidx + 1) strict
  _ -> not strict && hasLooseBVar b vidx

-- | Effectful memoized rebuild; like 'replaceE' but the callback may inspect an environment or raise a kernel error.
replaceIO :: (Expr -> Int -> IO (Maybe Expr)) -> Expr -> IO Expr
replaceIO f e0 = do
  cache <- newIORef (IM.empty :: IM.IntMap [(Expr, Int, Expr)])
  let go !off t = do
        r <- f t off
        case r of
          Just x -> pure x
          Nothing -> case t of
            App {} -> memo off t (step off t)
            Lam {} -> memo off t (step off t)
            Pi {} -> memo off t (step off t)
            Let {} -> memo off t (step off t)
            Proj {} -> memo off t (step off t)
            _ -> pure t
      memo off t k = do
        let key = exprHash t * 31 + off
        m <- readIORef cache
        case IM.lookup key m >>= lookupB t off of
          Just r -> pure r
          Nothing -> do
            r <- k
            modifyIORef' cache (IM.insertWith (++) key [(t, off, r)])
            pure r
      lookupB _ _ [] = Nothing
      lookupB t off ((u, o, r) : rest)
        | o == off && u == t = Just r
        | otherwise = lookupB t off rest
      step off t = case t of
        App fn a -> do
          fn' <- go off fn
          a' <- go off a
          pure (if ptrEq fn fn' && ptrEq a a' then t else App fn' a')
        Lam n bi d b -> do
          d' <- go off d
          b' <- go (off + 1) b
          pure (if ptrEq d d' && ptrEq b b' then t else Lam n bi d' b')
        Pi n bi d b -> do
          d' <- go off d
          b' <- go (off + 1) b
          pure (if ptrEq d d' && ptrEq b b' then t else Pi n bi d' b')
        Let n ty v b -> do
          ty' <- go off ty
          v' <- go off v
          b' <- go (off + 1) b
          pure (if ptrEq ty ty' && ptrEq v v' && ptrEq b b' then t else Let n ty' v' b')
        Proj n i x -> do
          x' <- go off x
          pure (if ptrEq x x' then t else Proj n i x')
        _ -> pure t
  go 0 e0

-- | Effectful traversal; shared subterms are visited once and the callback returns False to skip children.
forEachIO :: (Expr -> Int -> IO Bool) -> Expr -> IO ()
forEachIO f e0 = do
  seen <- newIORef IS.empty
  let compound = \case
        App {} -> True
        Lam {} -> True
        Pi {} -> True
        Let {} -> True
        Proj {} -> True
        _ -> False
      go !off t = do
        let k = exprHash t * 31 + off
        s <- readIORef seen
        if compound t && IS.member k s then pure () else do
          when (compound t) $ writeIORef seen (IS.insert k s)
          continue <- f t off
          when continue $ case t of
            App fn a -> go off fn >> go off a
            Lam _ _ d b -> go off d >> go (off + 1) b
            Pi _ _ d b -> go off d >> go (off + 1) b
            Let _ ty v b -> go off ty >> go off v >> go (off + 1) b
            Proj _ _ x -> go off x
            _ -> pure ()
  go 0 e0
