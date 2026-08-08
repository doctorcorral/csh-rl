{-# OPTIONS --guardedness #-}

-- | Master import for all CSHRL modules

module All where

-- Framework Core
import CSHRL.Core
import CSHRL.Finder

-- Probability (for stochastic extensions)
import CSHRL.Probability.Finite
import CSHRL.Core.Stochastic

-- Successor condition (CoinductiveHomomorphism) and analysis
import CSHRL.Core.CoinductiveHomomorphism
import CSHRL.Analysis.QLearningFailure

-- Stochastic dominance hierarchy and compositional algebra
import CSHRL.Probability.FOSD
import CSHRL.Probability.SD
import CSHRL.Probability.Convolution
import CSHRL.Probability.Compose
import CSHRL.Core.FOSD
import CSHRL.Core.SD
import CSHRL.Core.Compose
import CSHRL.Core.Abstraction

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
import CSHRL.Learning.Convergence
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
import CSHRL.Tasks.Verified.BinarySacrifice
import CSHRL.Tasks.Verified.SkillInvestment
import CSHRL.Tasks.Verified.PreparationDilemma
import CSHRL.Tasks.Verified.OnePlacement
import CSHRL.Tasks.Verified.Queens1
-- Queens8 and Queens8Learning omitted: full game-tree search (~4 min each).
-- Verified in a separate parallel CI job; run locally with:
--   agda src/CSHRL/Tasks/Verified/Queens8.agda
--   agda src/CSHRL/Tasks/Verified/Queens8Learning.agda

-- Stochastic Task Implementations
import CSHRL.Tasks.Stochastic.CoinFlip
import CSHRL.Tasks.Stochastic.GamblersRuin
import CSHRL.Tasks.Stochastic.RandomWalk
import CSHRL.Tasks.Stochastic.BiasedBandit
