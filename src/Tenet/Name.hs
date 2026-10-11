{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Hierarchical names, with a cached hash.
module Tenet.Name
  ( Name (..)
  , anonymous, mkStr, mkNum, nameOf, nameHash, isAnonymous
  , nameStr, appendAfter, appendIndexAfter, replacePrefix, isPrefixOf, appendName
  , namePrefix, nameLastStr
  , showName
  ) where

import Data.Bits (xor, shiftL, shiftR)
import Data.Char (isAlphaNum)
import qualified Data.Text as T
import Data.List (intercalate)

data Name
  = Anon
  | NStr !Int !Name !T.Text
  | NNum !Int !Name !Integer

anonymous :: Name
anonymous = Anon

nameHash :: Name -> Int
nameHash Anon = 1723
nameHash (NStr h _ _) = h
nameHash (NNum h _ _) = h

mix :: Int -> Int -> Int
mix a b = (a `xor` (b + 0x9e3779b9 + (a `shiftL` 6) + (a `shiftR` 2))) * 0x100000001b3

textHash :: T.Text -> Int
textHash = T.foldl' (\h c -> (h * 16777619) `xor` fromEnum c) 2166136261

mkStr :: Name -> T.Text -> Name
mkStr p s = NStr (mix (nameHash p) (textHash s)) p s

mkNum :: Name -> Integer -> Name
mkNum p n = NNum (mix (nameHash p) (fromInteger n + 77)) p n

-- | @nameOf ["Nat","add"]@
nameOf :: [T.Text] -> Name
nameOf = foldl mkStr Anon

nameStr :: T.Text -> Name
nameStr = mkStr Anon

isAnonymous :: Name -> Bool
isAnonymous Anon = True
isAnonymous _ = False

namePrefix :: Name -> Name
namePrefix Anon = Anon
namePrefix (NStr _ p _) = p
namePrefix (NNum _ p _) = p

nameLastStr :: Name -> Maybe T.Text
nameLastStr (NStr _ _ s) = Just s
nameLastStr _ = Nothing

instance Eq Name where
  a == b = nameHash a == nameHash b && eqN a b
    where
      eqN Anon Anon = True
      eqN (NStr _ p s) (NStr _ q t) = s == t && p == q
      eqN (NNum _ p m) (NNum _ q n) = m == n && p == q
      eqN _ _ = False

-- | A total order. Hash first (fast), structure to break ties; the order is not Lean's.
instance Ord Name where
  compare a b = case compare (nameHash a) (nameHash b) of
    EQ -> cmpN a b
    o -> o
    where
      cmpN Anon Anon = EQ
      cmpN Anon _ = LT
      cmpN _ Anon = GT
      cmpN (NStr _ p s) (NStr _ q t) = compare p q <> compare s t
      cmpN (NNum _ p m) (NNum _ q n) = compare p q <> compare m n
      cmpN (NStr {}) (NNum {}) = GT
      cmpN (NNum {}) (NStr {}) = LT

-- | Lean's @Name.appendAfter@: append to the last string component.
appendAfter :: Name -> T.Text -> Name
appendAfter (NStr _ p s) suf = mkStr p (s <> suf)
appendAfter n suf = mkStr n suf

-- | Lean's @Name.appendIndexAfter@.
appendIndexAfter :: Name -> Integer -> Name
appendIndexAfter (NStr _ p s) i = mkStr p (s <> "_" <> T.pack (show i))
appendIndexAfter n i = mkStr n ("_" <> T.pack (show i))

-- | Lean's @Name.replacePrefix@.
replacePrefix :: Name -> Name -> Name -> Name
replacePrefix n query new
  | isAnonymous n = if isAnonymous query then new else n
  | n == query = new
  | otherwise = case n of
      NStr _ p s -> mkStr (replacePrefix p query new) s
      NNum _ p k -> mkNum (replacePrefix p query new) k
      Anon -> n

-- | @isPrefixOf p n@: @p@ is a (not necessarily proper) prefix of @n@.
isPrefixOf :: Name -> Name -> Bool
isPrefixOf p = go
  where
    go n | n == p = True
         | isAnonymous n = False
         | otherwise = go (namePrefix n)

-- | @a.b + c.d = a.b.c.d@
appendName :: Name -> Name -> Name
appendName pre Anon = pre
appendName pre (NStr _ p s) = mkStr (appendName pre p) s
appendName pre (NNum _ p k) = mkNum (appendName pre p) k

showName :: Name -> String
showName Anon = "[anonymous]"
showName n = intercalate "." (reverse (go n))
  where
    go Anon = []
    go (NStr _ p s) = esc (T.unpack s) : go p
    go (NNum _ p k) = show k : go p
    esc s | not (null s), all (\c -> isAlphaNum c || c `elem` ("_'!?" :: String) || fromEnum c > 127) s = s
          | otherwise = "«" ++ s ++ "»"

instance Show Name where
  show = showName
