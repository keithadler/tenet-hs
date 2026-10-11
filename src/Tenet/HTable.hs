{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | A small mutable hash table with chained buckets. The caller supplies each key's hash and the equality
-- test, so keys can be pairs of expressions or expressions with offsets. Persistent maps were measured to
-- dominate checking time on shared-subterm-heavy inputs; this table does no allocation on lookup.
module Tenet.HTable (HTable, newHTable, lookupBy, insertH) where

import Control.Monad (forM_, when)
import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, getBounds, newArray)
import Data.Bits (shiftR, xor, (.&.))
import Data.IORef

data HTable v = HTable
  { htArr :: !(IORef (IOArray Int [(Int, v)]))
  , htCount :: !(IORef Int)
  }

-- | Spread a hash over all its bits before masking: the callers' hashes are cheap combinations whose low bits
-- are poorly distributed, which showed up as long bucket chains.
spread :: Int -> Int
spread h0 =
  let h1 = (h0 `xor` (h0 `shiftR` 32)) * 0x7fb5d329728ea185
      h2 = (h1 `xor` (h1 `shiftR` 29)) * 0x81dadef4bc2dd44d
  in h2 `xor` (h2 `shiftR` 32)
{-# INLINE spread #-}

newHTable :: IO (HTable v)
newHTable = do
  arr <- newArray (0, 63) []
  HTable <$> newIORef arr <*> newIORef 0

lookupBy :: HTable v -> Int -> (v -> Bool) -> IO (Maybe v)
lookupBy t h p = do
  arr <- readIORef (htArr t)
  (_, hi) <- getBounds arr
  bucket <- unsafeRead arr (spread h .&. hi)
  let go [] = Nothing
      go ((h', v) : rest) | h' == h && p v = Just v
                          | otherwise = go rest
  pure (go bucket)
{-# INLINE lookupBy #-}

insertH :: HTable v -> Int -> v -> IO ()
insertH t h v = do
  arr <- readIORef (htArr t)
  (_, hi) <- getBounds arr
  let size = hi + 1
  old <- unsafeRead arr (spread h .&. hi)
  unsafeWrite arr (spread h .&. hi) ((h, v) : old)
  n <- readIORef (htCount t)
  writeIORef (htCount t) (n + 1)
  when (n + 1 > 2 * size) $ do
    let size' = size * 4
    arr' <- newArray (0, size' - 1) []
    forM_ [0 .. size - 1] $ \i -> do
      bucket <- unsafeRead arr i
      forM_ bucket $ \ent@(h', _) -> do
        cur <- unsafeRead arr' (spread h' .&. (size' - 1))
        unsafeWrite arr' (spread h' .&. (size' - 1)) (ent : cur)
    writeIORef (htArr t) arr'
