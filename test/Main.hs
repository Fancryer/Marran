module Main (main) where
import Test.Hspec (hspec)
import Test.QuickCheck(generate, Arbitrary (arbitrary))
import Spec (spec, printExps)
import Utils (Pretty(pretty))
import qualified Data.Text as T

main :: IO ()
main = do
  hspec spec
  printExps
  pure ()