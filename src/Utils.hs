module Utils (
  mapFst,
  mapSnd,
  mapFstM,
  mapSndM,
  mapAccumM,
  uniqPreserveOrder,
  (|>),
  Zeroed(..),
  Pretty(..)
) where

import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

(|>) :: a -> (a -> b) -> b
(|>) a f = f a

mapFst :: (a -> t) -> (a, b) -> (t, b)
mapFst f (l, r) = (f l, r)

mapFstM :: Monad m => (a -> m t) -> (a, b) -> m (t, b)
mapFstM f (l, r) = do
  l' <- f l
  pure (l', r)

mapSnd :: (b -> t) -> (a, b) -> (a, t)
mapSnd f (l, r) = (l, f r)

mapSndM :: Monad m => (b -> m c) -> (a, b) -> m (a, c)
mapSndM f (l, r) = do
  r' <- f r
  pure (l, r')

mapAccumM :: Monad m => (s -> a -> m (b, s)) -> s -> [a] -> m ([b], s)
mapAccumM _ s [] = pure ([], s)
mapAccumM f s (x:xs) = do
  (y, s1) <- f s x
  (ys, s2) <- mapAccumM f s1 xs
  pure (y : ys, s2)

uniqPreserveOrder :: Ord a => [a] -> [a]
uniqPreserveOrder lst = reverse $ snd $ foldl go (Set.empty, []) lst
  where
    go (seen, acc) x
      | x `Set.member` seen = (seen, acc)
      | otherwise = (Set.insert x seen, x : acc)

class Zeroed a where zeroed :: a

class Pretty a where pretty :: a -> Text

instance Pretty a => Pretty (Maybe a) where
  pretty (Just a) = pretty a
  pretty _ = T.empty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left a) = pretty a
  pretty (Right b) = pretty b