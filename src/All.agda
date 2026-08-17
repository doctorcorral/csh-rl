{-# OPTIONS --guardedness #-}

-- | Master import for all CSHRL modules

module All where

-- Framework Core
import CSHRL.Core
import CSHRL.Finder

-- Probability (for stochastic extensions)
import CSHRL.Probability.Finite
import CSHRL.Core.Stochastic

-- Appendix (pedagogical and classical RL connection)
import appendix.PreservationEquivalence
import appendix.Arithmetic
import appendix.StochasticSubsumption

-- Environment Classes
import CSHRL.EnvironmentClass.FiniteDeterministicMDP
import CSHRL.EnvironmentClass.CombinatorialPlacementMDP
import CSHRL.EnvironmentClass.StochasticFiniteMDP

-- Learning Infrastructure
import CSHRL.Learning.Base
import CSHRL.Learning.FiniteDeterministicMDP
import CSHRL.Learning.StochasticFiniteMDP
import CSHRL.Learning.CombinatorialPlacementMDP

-- Classic Task Implementations (pedagogical, may use postulates)
import CSHRL.Tasks.Classic.DelayedGratification
import CSHRL.Tasks.Classic.Energy
import CSHRL.Tasks.Classic.KeyDoor
import CSHRL.Tasks.Classic.Maze
import CSHRL.Tasks.Classic.Queens
import CSHRL.Tasks.Classic.Trap

-- Verified Task Implementations
import CSHRL.Tasks.Verified.TwoState
import CSHRL.Tasks.Verified.TwoStateLearning
import CSHRL.Tasks.Verified.OnePlacement
import CSHRL.Tasks.Verified.Queens1
-- Queens8 and Queens8Learning omitted: full game-tree search (~4 min each).
-- Verified in a separate parallel CI job; run locally with:
--   agda src/CSHRL/Tasks/Verified/Queens8.agda
--   agda src/CSHRL/Tasks/Verified/Queens8Learning.agda
--
-- Synthesized tasks (Tasks/Synthesized/*) are demo/paper artifacts and are
-- checked outside this aggregate, in a separate parallel CI job.
-- Run locally with:
--   agda src/CSHRL/Tasks/Synthesized/SudokuSynth.agda         (4x4 dynamics learned)
--   agda src/CSHRL/Tasks/Synthesized/SudokuConceptSynth.agda  (4x4 conflict CONCEPT discovered, curated space)
--   agda src/CSHRL/Tasks/Synthesized/SudokuConceptEnum.agda   (concept identified from ALL 2^16 hypotheses; ~5 min)
--   agda src/CSHRL/Tasks/Synthesized/SudokuNonForced.agda     (non-forced: survival fails, Finder needed; seconds)
--   agda src/CSHRL/Tasks/Synthesized/Sudoku9Synth.agda        (9x9 learned, verified, solved by survival AND optimal Finder; ~9 min)

-- Stochastic Task Implementations
import CSHRL.Tasks.Stochastic.CoinFlip
import CSHRL.Tasks.Stochastic.GamblersRuin
import CSHRL.Tasks.Stochastic.RandomWalk
import CSHRL.Tasks.Stochastic.BiasedBandit
