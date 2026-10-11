{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | A small JSON parser, enough for NDJSON exports (no dependencies beyond the GHC boot libraries).
module Tenet.Json (Json (..), parseJson, field, fieldMaybe, asInt, asString, asArray, asBool) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.Char (chr, isDigit, ord)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TE

data Json
  = JNull
  | JBool !Bool
  | JNum !Integer
  | JStr !T.Text
  | JArr [Json]
  | JObj [(T.Text, Json)]
  deriving (Show)

-- | Parse one complete JSON value from a strict ByteString.
parseJson :: B.ByteString -> Either String Json
parseJson bs = case value (skipWs bs) of
  Left e -> Left e
  Right (v, rest) -> if B.null (skipWs rest) then Right v else Left "trailing characters after JSON value"

type P a = Either String (a, B.ByteString)

skipWs :: B.ByteString -> B.ByteString
skipWs = B.dropWhile (\w -> w == 32 || w == 9 || w == 10 || w == 13)

value :: B.ByteString -> P Json
value bs = case B.uncons bs of
  Nothing -> Left "unexpected end of input"
  Just (c, rest) -> case chr (fromIntegral c) of
    '{' -> object (skipWs rest) []
    '[' -> array (skipWs rest) []
    '"' -> do
      (s, r) <- str rest
      pure (JStr s, r)
    't' | BC.isPrefixOf "true" bs -> Right (JBool True, B.drop 4 bs)
    'f' | BC.isPrefixOf "false" bs -> Right (JBool False, B.drop 5 bs)
    'n' | BC.isPrefixOf "null" bs -> Right (JNull, B.drop 4 bs)
    ch | ch == '-' || isDigit ch -> number bs
    ch -> Left ("unexpected character " ++ show ch)

number :: B.ByteString -> P Json
number bs =
  let (neg, b1) = case BC.uncons bs of Just ('-', r) -> (True, r); _ -> (False, bs)
      (ds, r1) = BC.span isDigit b1
      -- skip a fraction and an exponent: exports only carry integers there
      r2 = case BC.uncons r1 of
             Just ('.', r) -> BC.dropWhile isDigit r
             _ -> r1
      r3 = case BC.uncons r2 of
             Just (e, r) | e == 'e' || e == 'E' -> BC.dropWhile (\x -> isDigit x || x == '+' || x == '-') r
             _ -> r2
      n = BC.foldl' (\acc d -> acc * 10 + toInteger (ord d - 48)) 0 ds
  in if B.null ds then Left "malformed number" else Right (JNum (if neg then negate n else n), r3)

str :: B.ByteString -> P T.Text
str bs =
  let (chunk, rest) = B.break (\w -> w == 34 || w == 92) bs
  in case B.uncons rest of
       Nothing -> Left "unterminated string"
       Just (34, r) -> Right (decode chunk, r)
       Just (_, r) -> escapes [chunk] r
  where
    decode = TE.decodeUtf8With TE.lenientDecode
    escapes acc r = case B.uncons r of
      Nothing -> Left "unterminated escape"
      Just (c, r1) -> do
        (piece, r2) <- case chr (fromIntegral c) of
          '"' -> Right ("\"", r1)
          '\\' -> Right ("\\", r1)
          '/' -> Right ("/", r1)
          'b' -> Right ("\b", r1)
          'f' -> Right ("\f", r1)
          'n' -> Right ("\n", r1)
          'r' -> Right ("\r", r1)
          't' -> Right ("\t", r1)
          'u' -> unicode r1
          _ -> Left "bad escape"
        let (chunk, rest) = B.break (\w -> w == 34 || w == 92) r2
            acc' = chunk : TE.encodeUtf8 piece : acc
        case B.uncons rest of
          Nothing -> Left "unterminated string"
          Just (34, r3) -> Right (decode (B.concat (reverse acc')), r3)
          Just (_, r3) -> escapes acc' r3
    hex4 b = if B.length b < 4 then Left "short \\u escape" else
      case mapM hexDigit (BC.unpack (B.take 4 b)) of
        Just ds -> Right (foldl (\a d -> a * 16 + d) 0 ds, B.drop 4 b)
        Nothing -> Left "bad \\u escape"
    hexDigit ch | isDigit ch = Just (ord ch - 48)
                | ch >= 'a' && ch <= 'f' = Just (ord ch - 87)
                | ch >= 'A' && ch <= 'F' = Just (ord ch - 55)
                | otherwise = Nothing
    unicode b = do
      (hi, r) <- hex4 b
      if hi >= 0xD800 && hi < 0xDC00
        then case BC.stripPrefix "\\u" r of
          Just r' -> do
            (lo, r'') <- hex4 r'
            if lo >= 0xDC00 && lo < 0xE000
              then Right (T.singleton (chr (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))), r'')
              else Right ("\xFFFD", r')
          Nothing -> Right ("\xFFFD", r)
        else Right (T.singleton (if hi >= 0xD800 && hi < 0xE000 then '\xFFFD' else chr hi), r)

array :: B.ByteString -> [Json] -> P Json
array bs acc = case B.uncons bs of
  Just (93, r) -> Right (JArr (reverse acc), r)
  _ -> do
    (v, r) <- value bs
    let r1 = skipWs r
    case B.uncons r1 of
      Just (44, r2) -> array (skipWs r2) (v : acc)
      Just (93, r2) -> Right (JArr (reverse (v : acc)), r2)
      _ -> Left "expected ',' or ']' in array"

object :: B.ByteString -> [(T.Text, Json)] -> P Json
object bs acc = case B.uncons bs of
  Just (125, r) -> Right (JObj (reverse acc), r)
  Just (34, r) -> do
    (k, r1) <- str r
    case B.uncons (skipWs r1) of
      Just (58, r2) -> do
        (v, r3) <- value (skipWs r2)
        let r4 = skipWs r3
        case B.uncons r4 of
          Just (44, r5) -> object (skipWs r5) ((k, v) : acc)
          Just (125, r5) -> Right (JObj (reverse ((k, v) : acc)), r5)
          _ -> Left "expected ',' or '}' in object"
      _ -> Left "expected ':' in object"
  _ -> Left "expected a string key in object"

fieldMaybe :: T.Text -> Json -> Maybe Json
fieldMaybe k (JObj kvs) = lookup k kvs
fieldMaybe _ _ = Nothing

field :: T.Text -> Json -> Either String Json
field k j = maybe (Left ("missing field '" ++ T.unpack k ++ "'")) Right (fieldMaybe k j)

asInt :: Json -> Either String Int
asInt (JNum n) = Right (fromInteger n)
asInt _ = Left "expected an integer"

asString :: Json -> Either String T.Text
asString (JStr s) = Right s
asString _ = Left "expected a string"

asArray :: Json -> Either String [Json]
asArray (JArr xs) = Right xs
asArray _ = Left "expected an array"

asBool :: Json -> Either String Bool
asBool (JBool b) = Right b
asBool _ = Left "expected a boolean"
