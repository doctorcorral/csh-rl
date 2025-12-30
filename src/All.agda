{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- All: Master import for all CSHRL modules
--
-- Includes both classic tasks (with postulates) and verified tasks.
------------------------------------------------------------------------

module All where

-- Framework Core
import CSHRL.Core
import CSHRL.Finder

-- Environment Classes
import CSHRL.EnvironmentClass.FiniteDeterministicMDP
import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

-- Verified Task Implementations (--safe, no postulates)
import CSHRL.Tasks.Verified.TwoState
import CSHRL.Tasks.Verified.OnePlacement
import CSHRL.Tasks.Verified.Queens1

-- Classic Task Implementations (with postulates for pedagogical purposes)
import CSHRL.Tasks.Classic.DelayedGratification
import CSHRL.Tasks.Classic.Energy
import CSHRL.Tasks.Classic.KeyDoor
import CSHRL.Tasks.Classic.Maze
import CSHRL.Tasks.Classic.Queens
import CSHRL.Tasks.Classic.Trap

-- Appendix
import appendix.PreservationEquivalence
