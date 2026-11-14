{-# LANGUAGE OverloadedStrings #-}

-- | "Did you mean?" suggestions for a name that is close to one in scope.
--
--   The distance is the optimal string alignment distance (Damerau--Levenshtein
--   with adjacent transpositions, which is the usual sense of a typo): swapping
--   two neighbouring characters counts as one edit, so @lenght@ is one edit
--   from @length@ and not two.  Plain Levenshtein calls that two and, for a
--   short name, misses it.
--
--   A candidate is offered when its distance is within 'threshold', which grows
--   with the length of the name.  A tie at the nearest distance is not broken
--   arbitrarily: an ambiguous suggestion is worse than none, so both are
--   suppressed.
module Suggest (
  distance,
  threshold,
  candidates,
  best,
  suggestionNote,
  typoNote
) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.List (sortOn, zip5)

-- | Optimal string alignment distance between two strings: insertions,
--   deletions, substitutions and transpositions of adjacent characters.
--
--   > distance "abc" "abc" == 0
--   > distance "lenght" "length" == 1
--   > distance "" "abc" == 3
--
--   The table is built one row at a time.  Row @i@ holds the distance from
--   @take i as@ to every prefix of @bs@, so it has @m + 1@ entries; an entry
--   depends on its left neighbour, on the entry above it and on the entry above
--   and to the left.  A transposition reaches two rows back, so the two
--   previous rows are kept.  Rows are combined with 'zip5' and 'scanl' rather
--   than indexed — identifiers are short, and an index that cannot go out of
--   bounds is worth more than the cells the zipping costs.
distance :: Text -> Text -> Int
distance a b = lastOr 0 (lastOr [] rows)
  where
    as = T.unpack a
    bs = T.unpack b
    m = length bs

    -- Row 0 is the distance from the empty prefix to every prefix of @bs@.
    firstRow = [0 .. m]

    -- A lazily built table.  Each row is computed from the two above it, and
    -- the third argument is the character two rows up, which the transposition
    -- rule compares against: it is 'Nothing' in the first row, where a
    -- transposition cannot apply.
    rows = firstRow : go 1 firstRow firstRow Nothing as

    go _ _ _ _ [] = []
    go i prev prevPrev mCa2 (ca : rest) =
      let row = nextRow i mCa2 ca prev prevPrev
      in row : go (i + 1) row prev (Just ca) rest

    -- The row for the next character of @a@.  'scanl' carries the entry to the
    -- left, which is the one value the zipped columns cannot supply; 'zip5'
    -- supplies the rest: the two characters of @bs@ involved, the entry above,
    -- the entry above and left, and the entry two rows above and two columns
    -- left.
    nextRow i mCa2 ca prev prevPrev =
      scanl (cell ca mCa2) i $
        zip5
          bs
          (Nothing : map Just bs)
          (drop 1 prev)
          prev
          (Nothing : map Just prevPrev)

    cell ca mCa2 left (cb, mCb2, up, diag, mDiag2)
      | ca == cb = diag
      | Just ca2 <- mCa2
      , Just cb2 <- mCb2
      , Just diag2 <- mDiag2
      , ca == cb2
      , ca2 == cb = 1 + diag2
      | otherwise = 1 + minimum [up, left, diag]

-- | The last element of a list, or the default when it is empty.  The table
--   above always has at least one row of at least one entry, so the defaults
--   are never reached; they are there so that the function is total.
lastOr :: a -> [a] -> a
lastOr def = foldl (\_ x -> x) def

-- | How far a typo may be from the name it mistypes: one edit for a short name,
--   more for a long one, so that @freezeRowMutiIn@ can still suggest
--   @freezeRowMutIn@.
threshold :: Text -> Int
threshold name = max 1 (T.length name `div` 3)

-- | The names within 'threshold' of the target, nearest first.  At most three
--   are returned, and the target itself is never among them.
candidates :: [Text] -> Text -> [Text]
candidates names target =
  take 3 . map snd . sortOn fst $
    [ (d, n)
    | n <- names
    , n /= target
    , let d = distance target n
    , d <= threshold target
    ]

-- | The single best candidate, or 'Nothing' when there is none or when the
--   nearest distance is shared.
--
--   Silence on a tie is deliberate: @par@ is one edit from both @var@ and
--   @say@, and picking one of them by the order of a map teaches the user the
--   wrong name.
best :: [Text] -> Text -> Maybe Text
best names target =
  case candidates names target of
    [] -> Nothing
    (c:rest)
      | any ((== distance target c) . distance target) rest -> Nothing
      | otherwise -> Just c

-- | The note a diagnostic carries, if a suggestion is worth making.
suggestionNote :: [Text] -> Text -> Maybe Text
suggestionNote names target =
  case best names target of
    Nothing -> Nothing
    Just n  -> Just ("did you mean `" <> n <> "`?")

-- | A stricter variant for the one place where a suggestion is allowed to turn
--   a previously accepted program into an error: an undeclared type name.
--
--   There, an opaque type is legitimate (a program may name a type it does not
--   declare), so a hint must be unambiguous in a stronger sense than usual: the
--   name must be exactly one edit from the declared one, that candidate must be
--   the only one at that distance, and the name must be long enough for a
--   single edit to be a typo rather than a coincidence.  @Foo@ next to @Food@ is
--   therefore left alone, while @Prise@ next to @Price@ is reported.
typoNote :: [Text] -> Text -> Maybe Text
typoNote names target
  | T.length target < 4 = Nothing
  | otherwise = case best names target of
      Just n | distance target n == 1 -> Just ("did you mean `" <> n <> "`?")
      _ -> Nothing
