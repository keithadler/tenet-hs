{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Universe levels: construction, normalization, and the kernel's notion of level equality.
module Tenet.Level
  ( Level (..)
  , lOne, mkSucc, mkMax, mkIMax
  , isExplicit, toOffset, isNotZero, normalizesToZero
  , instantiateLevel, getUndefParam, levelHasParam, levelHash
  , isEquiv, isGeq, normalize, levelsEquiv
  , showLevel
  ) where

import Data.Bits (xor)
import Data.List (sortBy)
import Tenet.Name

data Level
  = LZero
  | LSucc !Level
  | LMax !Level !Level
  | LIMax !Level !Level
  | LParam !Name
  deriving (Eq)

lOne :: Level
lOne = LSucc LZero

levelHash :: Level -> Int
levelHash LZero = 0x2a
levelHash (LSucc l) = 1 * 1000003 `xor` levelHash l * 31 + 1
levelHash (LMax a b) = (2 * 1000003 `xor` levelHash a) * 31 + levelHash b
levelHash (LIMax a b) = (3 * 1000003 `xor` levelHash a) * 37 + levelHash b
levelHash (LParam n) = 4 * 1000003 `xor` nameHash n

levelHasParam :: Level -> Bool
levelHasParam LZero = False
levelHasParam (LSucc l) = levelHasParam l
levelHasParam (LMax a b) = levelHasParam a || levelHasParam b
levelHasParam (LIMax a b) = levelHasParam a || levelHasParam b
levelHasParam (LParam _) = True

depth :: Level -> Int
depth LZero = 0
depth (LSucc l) = 1 + depth l
depth (LMax a b) = 1 + max (depth a) (depth b)
depth (LIMax a b) = 1 + max (depth a) (depth b)
depth (LParam _) = 0

mkSucc :: Level -> Int -> Level
mkSucc l k = iterate LSucc l !! k

isExplicit :: Level -> Bool
isExplicit LZero = True
isExplicit (LSucc l) = isExplicit l
isExplicit _ = False

toOffset :: Level -> (Level, Int)
toOffset = go 0
  where
    go !k (LSucc l) = go (k + 1) l
    go !k l = (l, k)

-- | Simplifying max, as the Lean kernel's @mk_max@.
mkMax :: Level -> Level -> Level
mkMax l1 l2
  | isExplicit l1 && isExplicit l2 = if snd (toOffset l1) >= snd (toOffset l2) then l1 else l2
  | l1 == l2 = l1
  | l1 == LZero = l2
  | l2 == LZero = l1
  | LMax a b <- l2, a == l1 || b == l1 = l2
  | LMax a b <- l1, a == l2 || b == l2 = l1
  | (b1, k1) <- toOffset l1, (b2, k2) <- toOffset l2, b1 == b2 = if k1 > k2 then l1 else l2
  | otherwise = LMax l1 l2

-- | Simplifying imax, as the Lean kernel's @mk_imax@.
mkIMax :: Level -> Level -> Level
mkIMax l1 l2
  | isNotZero l2 = mkMax l1 l2
  | l2 == LZero = l2
  | l1 == LZero || l1 == lOne = l2
  | l1 == l2 = l1
  | otherwise = LIMax l1 l2

-- | Provably nonzero for every parameter assignment.
isNotZero :: Level -> Bool
isNotZero (LSucc _) = True
isNotZero (LMax a b) = isNotZero a || isNotZero b
isNotZero (LIMax _ b) = isNotZero b
isNotZero _ = False

-- | Normalizes to zero (denotes @Prop@).
normalizesToZero :: Level -> Bool
normalizesToZero LZero = True
normalizesToZero (LMax a b) = normalizesToZero a && normalizesToZero b
normalizesToZero (LIMax _ b) = normalizesToZero b
normalizesToZero _ = False

instantiateLevel :: [Name] -> [Level] -> Level -> Level
instantiateLevel ps ls = go
  where
    go l | not (levelHasParam l) = l
    go (LParam n) = case lookup n (zip ps ls) of
      Just r -> r
      Nothing -> LParam n
    go (LSucc l) = LSucc (go l)
    go (LMax a b) = mkMax (go a) (go b)
    go (LIMax a b) = mkIMax (go a) (go b)
    go l = l

getUndefParam :: [Name] -> Level -> Maybe Name
getUndefParam ps = go
  where
    go l | not (levelHasParam l) = Nothing
    go (LParam n) = if n `elem` ps then Nothing else Just n
    go (LSucc l) = go l
    go (LMax a b) = maybe (go b) Just (go a)
    go (LIMax a b) = maybe (go b) Just (go a)
    go _ = Nothing

-- | The kernel's level equality: structural, or equal after normalization.
isEquiv :: Level -> Level -> Bool
isEquiv a b = a == b || normalize a == normalize b

levelsEquiv :: [Level] -> [Level] -> Bool
levelsEquiv as bs = length as == length bs && and (zipWith isEquiv as bs)

-- | Sound, incomplete: @l1@ is at least @l2@ for every parameter assignment.
isGeq :: Level -> Level -> Bool
isGeq l1 l2 = geqCore (normalize l1) (normalize l2)

geqCore :: Level -> Level -> Bool
geqCore l1 l2
  | l1 == l2 || l2 == LZero = True
  | LMax a b <- l2 = isGeq l1 a && isGeq l1 b
  | LMax a b <- l1, isGeq a l2 || isGeq b l2 = True
  | LIMax a b <- l2 = isGeq l1 a && isGeq l1 b
  | LIMax _ b <- l1 = isGeq b l2
  | otherwise =
      let (b1, k1) = toOffset l1
          (b2, k2) = toOffset l2
      in if | b1 == b2 || b2 == LZero -> k1 >= k2
            | k1 == k2 && k1 > 0 -> isGeq b1 b2
            | otherwise -> False

-- | Put a level into the kernel's normal form.
normalize :: Level -> Level
normalize l = case toOffset l of
  (LZero, _) -> l
  (LParam _, _) -> l
  (LIMax a b, k) -> mkSucc (mkIMax (normalize a) (normalize b)) k
  (r@(LMax _ _), k) ->
    let todo = pushMax r []
        args0 = concatMap (\a -> pushMax (normalize a) []) todo
        args = sortBy normCmp args0
        i0 = start args
        rest = drop i0 args
        merged = case rest of
          (r0 : rs) -> mergeBases r0 rs
          [] -> []
    in mkMaxList (map (`mkSucc` k) merged)
  _ -> l
  where
    -- skip leading explicit levels subsumed by a later, larger-offset one
    start args = case args of
      (a : _) | isExplicit a ->
        let ex = takeWhile isExplicit args
            i = length ex - 1
            kk = snd (toOffset (args !! i))
            tailArgs = drop (i + 1) args
            subsumed = any (\x -> snd (toOffset x) >= kk) tailArgs
        in if subsumed then i + 1 else i
      _ -> 0
    mergeBases first xs = go first xs
      where
        go cur [] = [cur]
        go cur (y : ys)
          | fst (toOffset cur) == fst (toOffset y) =
              if snd (toOffset cur) < snd (toOffset y) then go y ys else go cur ys
          | otherwise = cur : go y ys

pushMax :: Level -> [Level] -> [Level]
pushMax (LMax a b) acc = pushMax a (pushMax b acc)
pushMax l acc = l : acc

mkMaxList :: [Level] -> Level
mkMaxList [x] = x
mkMaxList xs = foldr1 mkMax xs

kindRank :: Level -> Int
kindRank LZero = 0
kindRank (LSucc _) = 1
kindRank (LMax _ _) = 2
kindRank (LIMax _ _) = 3
kindRank (LParam _) = 4

-- | The total order used by normalization: zero least, succ immediate.
normLt :: Level -> Level -> Bool
normLt a b =
  let (l1, k1) = toOffset a
      (l2, k2) = toOffset b
  in if l1 /= l2
       then if kindRank l1 /= kindRank l2
              then kindRank l1 < kindRank l2
              else case (l1, l2) of
                (LParam p, LParam q) -> p < q
                (LMax a1 b1, LMax a2 b2) -> if a1 == a2 then normLt b1 b2 else normLt a1 a2
                (LIMax a1 b1, LIMax a2 b2) -> if a1 == a2 then normLt b1 b2 else normLt a1 a2
                _ -> False
       else k1 < k2

normCmp :: Level -> Level -> Ordering
normCmp x y
  | x == y = EQ
  | normLt x y = LT
  | normLt y x = GT
  | otherwise = EQ

showLevel :: Level -> String
showLevel l
  | isExplicit l = show (depth l)
  | otherwise = case l of
      LParam n -> showName n
      LSucc _ -> let (b, k) = toOffset l in child b ++ "+" ++ show k
      LMax a b -> "max " ++ child a ++ " " ++ child b
      LIMax a b -> "imax " ++ child a ++ " " ++ child b
      LZero -> "0"
  where
    child x | isExplicit x = showLevel x
            | LParam _ <- x = showLevel x
            | otherwise = "(" ++ showLevel x ++ ")"

instance Show Level where
  show = showLevel
