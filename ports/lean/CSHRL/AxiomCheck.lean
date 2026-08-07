/-
CSHRL portability kernel, Lean 4 port.
Conformance check: kernel theorems may depend only on Lean's built-in
axioms (propext, Quot.sound, and Classical.choice via omega) -- crucially,
no sorryAx: every proof is complete.
-/

import CSHRL.Streams
import CSHRL.Core
import CSHRL.BinarySacrifice
import CSHRL.SkillInvestment
import CSHRL.PreparationDilemma
import CSHRL.Subsumption
import CSHRL.Learning
import CSHRL.Convergence
import CSHRL.QLearningFailure
import CSHRL.Dist
import CSHRL.Lex
import CSHRL.SDHierarchy
import CSHRL.Convolution
import CSHRL.Ranking
import CSHRL.Abstraction

namespace CSHRL

-- T1
#print axioms dominance_unfold
#print axioms dominance_coind
-- T2
#print axioms decomposition
-- T3
#print axioms sacrifice_coinductive_homomorphism
#print axioms no_coindhomo_forward
#print axioms no_coindhomo_backward
#print axioms skill_coinductive_homomorphism
#print axioms skill_no_coindhomo_forward
#print axioms skill_no_coindhomo_backward
#print axioms prep_coinductive_homomorphism
#print axioms prep_no_coindhomo_forward
#print axioms prep_no_coindhomo_backward
-- T4
#print axioms subsumes_partial_sum
#print axioms subsumes_successor_return
-- T5
#print axioms swap_fixes_pair
#print axioms demote_preserves_dominance
-- T6
#print axioms q_learning_picks_inferior_successor
-- T7
#print axioms swap_adjacent_decreases
#print axioms fixFirst_progress
#print axioms swap_convergence_bound
#print axioms violations_zero_iff
#print axioms learn_realizes_oracle
-- T8
#print axioms lex_unfold
#print axioms dominance_lex
#print axioms pointwise_homo_stochastic
-- T9
#print axioms SD_subsumes
#print axioms SD_append
#print axioms SD_scale
-- T10
#print axioms FOSD_conv
#print axioms FOSD_SD_conv
-- T11
#print axioms rankingSubsumes
#print axioms productRanking
#print axioms convProduct
#print axioms sumRanking
-- T12
#print axioms abstractLift
#print axioms abstractConvProduct

end CSHRL
