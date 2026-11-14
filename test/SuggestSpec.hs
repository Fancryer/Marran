{-# LANGUAGE OverloadedStrings #-}

-- | The suggestion machinery: the distance, the threshold and, most
--   importantly, the cases in which nothing is suggested.  A wrong suggestion
--   is worse than no suggestion, so the silence cases are tested as carefully
--   as the hits.
module SuggestSpec (sSpec) where

import qualified Data.Map as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Text as T
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, elements, forAll, listOf, (===))

import Suggest

sSpec :: Spec
sSpec = describe "suggestions" $ do

  describe "distance" $ do
    it "is zero for the same string" $
      distance "counter" "counter" `shouldBe` 0

    it "counts a substitution as one edit" $
      distance "counter" "counver" `shouldBe` 1

    it "counts an insertion as one edit" $
      distance "lenght" "lengthx" `shouldBe` 2

    it "counts a transposition as one edit, not two" $
      distance "lenght" "length" `shouldBe` 1

    it "counts deleting every character" $
      distance "" "abc" `shouldBe` 3

    it "is symmetric" $
      distance "make" "kcae" `shouldBe` distance "kcae" "make"

    prop "agrees with the table implementation it replaced" $
      forAll shortName $ \xs ->
        forAll shortName $ \ys ->
          distance (T.pack xs) (T.pack ys)
            === referenceDistance (T.pack xs) (T.pack ys)

    prop "never exceeds the length of the longer string" $
      forAll shortName $ \xs ->
        forAll shortName $ \ys ->
          distance (T.pack xs) (T.pack ys)
            <= max (length xs) (length ys)

  describe "threshold" $ do
    it "allows one edit for a short name" $
      threshold "x" `shouldBe` 1

    it "grows with the length of the name" $
      threshold "freezeRowMutIn" `shouldBe` 4

  describe "best" $ do
    it "suggests a name one edit away" $
      best ["counter", "make"] "countr" `shouldBe` Just "counter"

    it "suggests across a transposition" $
      best ["counter"] "conuter" `shouldBe` Just "counter"

    it "stays silent when nothing is close" $
      best ["counter", "make"] "zzzz" `shouldBe` Nothing

    it "stays silent when two names are equally close" $
      best ["var", "say"] "vay" `shouldBe` Nothing

    it "never suggests the name itself" $
      best ["counter"] "counter" `shouldBe` Nothing

  describe "candidates" $ do
    it "returns the nearest first" $
      candidates ["abcd", "abce", "abcf"] "abcg"
        `shouldBe` ["abcd", "abce", "abcf"]

    it "returns at most three" $
      length (candidates ["aa", "ab", "ac", "ad", "ae"] "a?") `shouldBe` 3

    it "returns nothing for a distant name" $
      candidates ["counter"] "zzzz" `shouldBe` []

  describe "typoNote" $ do
    it "suggests a declared type one edit away" $
      typoNote ["Price"] "Prise" `shouldBe` Just "did you mean `Price`?"

    it "stays silent for a short name, where one edit is a coincidence" $
      typoNote ["Food"] "Foo" `shouldBe` Nothing

    it "stays silent when two types are one edit away" $
      typoNote ["Price", "Prick"] "Pric" `shouldBe` Nothing

    it "stays silent when the nearest type is two edits away" $
      typoNote ["Price"] "Prlcex" `shouldBe` Nothing

  describe "suggestionNote" $ do
    it "words the note the way the diagnostics expect" $
      suggestionNote ["counter"] "countr"
        `shouldBe` Just "did you mean `counter`?"

    it "produces no note when there is no candidate" $
      suggestionNote ["counter"] "zzzz" `shouldBe` Nothing

-- | Short names over a tiny alphabet: the alphabet is small enough that
--   transpositions and tie cases actually occur, and the names are short
--   enough for the quadratic oracle below.
shortName :: Gen String
shortName = listOf (elements "abc")

-- | The table implementation that 'distance' used before it was rewritten
--   without indexing, kept as an oracle: it is a direct transcription of the
--   recurrence and shares no code with the version under test.
--
--   The table is a lazy map, so the entries can refer to each other; every
--   lookup is of an entry the table already contains.
referenceDistance :: T.Text -> T.Text -> Int
referenceDistance a b = at n m
  where
    as = T.unpack a
    bs = T.unpack b
    n = length as
    m = length bs

    charAt xs i = listToMaybe (drop i xs)

    table = Map.fromList [ ((i, j), entry i j) | i <- [0 .. n], j <- [0 .. m] ]

    at i j = fromMaybe 0 (Map.lookup (i, j) table)

    entry 0 j = j
    entry i 0 = i
    entry i j
      | charAt as (i - 1) == charAt bs (j - 1) = at (i - 1) (j - 1)
      | transposed = 1 + at (i - 2) (j - 2)
      | otherwise = 1 + minimum [
            at (i - 1) j
          , at i (j - 1)
          , at (i - 1) (j - 1)
          ]
      where
        transposed =
          i > 1 && j > 1
            && charAt as (i - 1) == charAt bs (j - 2)
            && charAt as (i - 2) == charAt bs (j - 1)
