import Erdos767.Basic
import Erdos767.Arithmetic
import Erdos767.GraphBasics
import Erdos767.Constructions
import Erdos767.Chapter3
import Erdos767.SplitPathFan

/-!
# Complete executable entry point for Chapter 3

This module gathers every Chapter 3 definition, arithmetic lemma, extremal
construction, exact edge count, forbidden-path-fan proof, and
manuscript-facing theorem.  The proofs remain in the focused modules imported
above; importing this one file makes the complete Chapter 3 API available.
-/

namespace Erdos767

#check nearlyRegularGraph_card_edgeFinset_eq_t
#check nearlyRegularGraph_pathFanFree
#check splitGraph_card_edgeFinset_eq
#check splitGraph_pathFanFree
#check p_eq_terminal
#check h_eq_piecewise_real
#check linear_bound_real
#check h_le_mul_sub_one_of_p_lt_h
#check merge_ineq_both
#check cycle_arithmetic_consequences
#check small_c_arithmetic

end Erdos767
