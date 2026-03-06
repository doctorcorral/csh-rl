#!/bin/bash
# Build order to avoid Agda 2.8.0 serialization bug (__IMPOSSIBLE__ in Common.hs).
# Run from repo root. Order matters for cache consistency.
set -e
cd "$(dirname "$0")/.."
agda src/CSHRL/Utils/NatArithmetic.agda
agda src/CSHRL/Synthesis/AutoFeatureNat.agda
agda src/CSHRL/Core.agda
agda src/CSHRL/Probability/Finite.agda
agda src/CSHRL/Probability/FOSD.agda
agda src/CSHRL/Core/Stochastic.agda
agda src/CSHRL/Core/FOSD.agda
agda src/CSHRL/EnvironmentClass/StochasticFiniteMDP.agda
agda src/CSHRL/EnvironmentClass/CombinatorialPlacementMDP.agda
agda src/CSHRL/Learning/Base.agda
agda src/CSHRL/Synthesis/Core.agda
agda src/CSHRL/Synthesis/FiniteDeterministicMDP.agda
agda src/CSHRL/Synthesis/StochasticFiniteMDP.agda
agda src/CSHRL/Synthesis/FOSDStochasticFiniteMDP.agda
agda src/CSHRL/EnvironmentClass/FiniteDeterministicMDP.agda
# Task modules that are dependencies of other tasks (avoids serialization bug)
agda src/CSHRL/Tasks/Synthesized/CliffWalkE2E.agda
agda src/CSHRL/Tasks/Stochastic/GamblersRuin.agda
agda src/CSHRL/Tasks/Stochastic/GamblersRuinFOSDSynth.agda
echo "Dependencies OK. You can now compile any task module."
