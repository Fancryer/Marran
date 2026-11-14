{-# LANGUAGE OverloadedRecordDot #-}

-- | The graph generators that feed the snapshot benchmark.  A generator is
--   judged by the shape of the graph it describes, so the tests check the
--   shape rather than the order in which the edges happen to be emitted.
module BenchmarkSpec (benchSpec) where

import Control.Monad (forM_)
import Data.List (sort)
import Test.Hspec

import Benchmark (
    GraphConfig (..),
    GraphKind (..),
    SnapshotGraph (..),
    generateGraph
  )

benchSpec :: Spec
benchSpec = describe "benchmark graphs" $ do

  describe "generateTree" $ do
    it "gives every node except the root exactly one parent" $
      forM_ treeConfigs $ \config ->
        withGraph config $ \g ->
          sort (map snd g.edges) `shouldBe` [1 .. g.nodeCount - 1]

    it "has one node for every prefix of every level" $
      forM_ treeConfigs $ \config ->
        withGraph config $ \g ->
          g.nodeCount `shouldBe`
            sum [branching config ^ level | level <- [0 .. depth config]]

    it "points every edge from a lower identifier to a higher one" $
      forM_ treeConfigs $ \config ->
        withGraph config $ \g ->
          all (\(from, to) -> from < to) g.edges `shouldBe` True

  it "rejects a negative depth" $
    generateGraph (GraphConfig Tree (-1) 2)
      `shouldBe` Left "Graph depth must be non-negative"

  it "rejects a branching factor below one" $
    generateGraph (GraphConfig Tree 2 0)
      `shouldBe` Left "Graph branching factor must be positive"

-- | The configurations a small tree can have, including the two degenerate
--   ones: a tree of depth zero (the root alone) and a chain (branching one).
treeConfigs :: [GraphConfig]
treeConfigs = [GraphConfig Tree d b | d <- [0 .. 5], b <- [1 .. 4]]

withGraph :: GraphConfig -> (SnapshotGraph -> Expectation) -> Expectation
withGraph config check =
  case generateGraph config of
    Left err -> expectationFailure err
    Right g -> check g
