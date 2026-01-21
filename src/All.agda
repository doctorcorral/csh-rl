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

-- Classic Task Implementations (pedagogical, may use postulates)
import CSHRL.Tasks.Classic.DelayedGratification
import CSHRL.Tasks.Classic.Energy
import CSHRL.Tasks.Classic.KeyDoor
import CSHRL.Tasks.Classic.Maze
import CSHRL.Tasks.Classic.Queens
import CSHRL.Tasks.Classic.Trap

-- Verified Task Implementations
import CSHRL.Tasks.Verified.TwoState
import CSHRL.Tasks.Verified.OnePlacement
import CSHRL.Tasks.Verified.Queens1

-- Stochastic Task Implementations
import CSHRL.Tasks.Stochastic.CoinFlip
import CSHRL.Tasks.Stochastic.GamblersRuin
import CSHRL.Tasks.Stochastic.RandomWalk
import CSHRL.Tasks.Stochastic.BiasedBandit
