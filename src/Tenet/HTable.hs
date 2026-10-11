{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | A lossy, direct-mapped table. Each hash selects exactly one slot; inserting overwrites whatever was there.
-- Every use in this checker (the infer, whnf and unfold caches, the sets of equalities already decided, the
-- memo tables of substitution and of equality) only ever skips work, so forgetting an entry costs time and never
-- changes an answer. In exchange there are no chains to walk, nothing to allocate per insert beyond the value
-- itself, and memory is bounded: the table grows only up to a cap, where a chained table keeps every entry for
-- the life of the checker (10.9 GB on one of the arena's performance tests).
module Tenet.HTable (HTable, newHTable, lookupBy, insertH) where

import Control.Monad (forM_, when)
import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, IOUArray, getBounds, newArray)
import Data.Bits (shiftR, xor, (.&.), (.|.))
import Data.IORef

data HTable v = HTable
  { htKeys :: !(IORef (IOUArray Int Int))   -- ^ stored hash with the low bit set; 0 marks an empty slot
  , htVals :: !(IORef (IOArray Int v))
  , htInserts :: !(IORef Int)
  }

-- | Spread a hash over all its bits before masking: the callers' hashes are cheap combinations whose low bits
-- are poorly distributed.
spread :: Int -> Int
spread h0 =
  let h1 = (h0 `xor` (h0 `shiftR` 32)) * 0x7fb5d329728ea185
      h2 = (h1 `xor` (h1 `shiftR` 29)) * 0x81dadef4bc2dd44d
  in h2 `xor` (h2 `shiftR` 32)
{-# INLINE spread #-}

initialSize, maxSize :: Int
initialSize = 32
maxSize = 1048576

newHTable :: IO (HTable v)
newHTable = do
  ks <- newArray (0, initialSize - 1) 0
  vs <- newArray (0, initialSize - 1) emptySlot
  HTable <$> newIORef ks <*> newIORef vs <*> newIORef 0

emptySlot :: a
emptySlot = error "HTable: read an empty slot"

lookupBy :: HTable v -> Int -> (v -> Bool) -> IO (Maybe v)
lookupBy t h p = do
  ks <- readIORef (htKeys t)
  (_, hi) <- getBounds ks
  let hk = h .|. 1
      i = spread hk .&. hi
  k <- unsafeRead ks i
  if k /= hk then pure Nothing else do
    vs <- readIORef (htVals t)
    v <- unsafeRead vs i
    pure (if p v then Just v else Nothing)
{-# INLINE lookupBy #-}

insertH :: HTable v -> Int -> v -> IO ()
insertH t h v = do
  ks <- readIORef (htKeys t)
  (_, hi) <- getBounds ks
  let hk = h .|. 1
      i = spread hk .&. hi
  vs <- readIORef (htVals t)
  unsafeWrite ks i hk
  unsafeWrite vs i v
  n <- readIORef (htInserts t)
  writeIORef (htInserts t) (n + 1)
  -- grow while the table is being used hard and is below its cap; entries that collide while rehashing are lost
  let size = hi + 1
  when (n + 1 > 1 * size && size < maxSize) $ do
    let size' = size * 4
    ks' <- newArray (0, size' - 1) 0
    vs' <- newArray (0, size' - 1) emptySlot
    forM_ [0 .. size - 1] $ \j -> do
      k <- unsafeRead ks j
      when (k /= 0) $ do
        x <- unsafeRead vs j
        let i' = spread k .&. (size' - 1)
        unsafeWrite ks' i' k
        unsafeWrite vs' i' x
    writeIORef (htKeys t) ks'
    writeIORef (htVals t) vs'
    writeIORef (htInserts t) 0
