{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | The name, level and expression tables of an export: dense growable arrays, because on a large export a
-- persistent map costs about as much per entry as the term it points to. Indices may be sparse or out of order,
-- as the format allows; an index far beyond the dense range goes to an overflow map instead of growing the array.
--
-- Entries are only ever added, and a line refers only to entries added by earlier lines, so reading through
-- 'lookupT' from pure code is sound: whatever it sees was written before the line being parsed.
module Tenet.Table (Table, newTable, insertT, lookupT) where

import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, IOUArray, getBounds, newArray)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import System.IO.Unsafe (unsafeDupablePerformIO)

data Table a = Table
  { tVals :: !(IORef (IOArray Int a))
  , tUsed :: !(IORef (IOUArray Int Bool))
  , tOverflow :: !(IORef (IM.IntMap a))
  }

newTable :: IO (Table a)
newTable = do
  vs <- newArray (0, 1023) (error "Table: empty slot")
  us <- newArray (0, 1023) False
  Table <$> newIORef vs <*> newIORef us <*> newIORef IM.empty

-- | Add an entry. Returns False if the index is already defined.
insertT :: Table a -> Int -> a -> IO Bool
insertT t i v
  | i < 0 = pure False
  | otherwise = do
      vs <- readIORef (tVals t)
      (_, hi) <- getBounds vs
      let cap = hi + 1
      if i < cap then dense vs i
      else if i < 2 * cap + 1024 then do
        let cap' = max (2 * cap) (i + 1)
        vs' <- newArray (0, cap' - 1) (error "Table: empty slot")
        us <- readIORef (tUsed t)
        us' <- newArray (0, cap' - 1) False
        let copy j | j >= cap = pure ()
                   | otherwise = do
                       u <- unsafeRead us j
                       if u then unsafeRead vs j >>= unsafeWrite vs' j >> unsafeWrite us' j True else pure ()
                       copy (j + 1)
        copy 0
        writeIORef (tVals t) vs'
        writeIORef (tUsed t) us'
        dense vs' i
      else do
        o <- readIORef (tOverflow t)
        if IM.member i o then pure False else writeIORef (tOverflow t) (IM.insert i v o) >> pure True
  where
    dense vs j = do
      us <- readIORef (tUsed t)
      u <- unsafeRead us j
      if u then pure False else unsafeWrite vs j v >> unsafeWrite us j True >> pure True

lookupT :: Table a -> Int -> Maybe a
lookupT t i = unsafeDupablePerformIO $ do
  vs <- readIORef (tVals t)
  (_, hi) <- getBounds vs
  if i >= 0 && i <= hi
    then do
      us <- readIORef (tUsed t)
      u <- unsafeRead us i
      if u then Just <$> unsafeRead vs i else IM.lookup i <$> readIORef (tOverflow t)
    else IM.lookup i <$> readIORef (tOverflow t)
{-# NOINLINE lookupT #-}
