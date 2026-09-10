import Erdos767.BaseRange
import Erdos767.FinalArithmetic

/-!
# Final manuscript interface (PDF supplied on 2026-09-10)

The final paper renames `A, t, p, h` to `I, R, J, F` and reorders the
numbered results. This namespace exposes that notation without changing
the existing proof API. The nine literature hypotheses remain explicit.

Natural subtraction in `splitTerm` agrees with integer subtraction when
`a ≤ n`, in particular throughout the main theorem's range `k + 2 ≤ n`.
For `n < a`, the implementation of `J` is a natural-number extension,
not the signed expression in the PDF. `F` uses `n.choose 2` in that range.
-/

namespace Erdos767.FinalPaper

universe u

/-- The final manuscript's admissible set `I_k`. -/
abbrev I (k : ℕ) : Finset ℕ := A k
/-- The nearly regular count `R_k(n)`. -/
abbrev R (k n : ℕ) : ℕ := t k n
/-- The split maximum `J_k(n)`, used for `n ≥ k + 2`. -/
abbrev J (k n : ℕ) : ℕ := p k n
/-- The piecewise comparison function `F_k(n)`. -/
abbrev F (k n : ℕ) : ℕ := h k n

@[simp] theorem mem_I_iff {k a : ℕ} :
    a ∈ I k ↔ (k + 1) / 2 + 1 ≤ a ∧ a ≤ k + 1 := mem_A_iff

theorem F_eq_max {k n : ℕ} (hn : k + 2 ≤ n) :
    F k n = max (R k n) (J k n) := h_eq_max hn

/-- Theorem 1.3: the exact bound includes an attaining graph. -/
theorem theorem_1_3 (lit : LiteratureTheorems.{u})
    {k n : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    ExactUniversalEdgeBound.{u} (k + 2) n (F k n) :=
  main_theorem_of_literature lit hk hn

/-- The displayed maximum in Theorem 1.3, including the `k = 1` case. -/
theorem theorem_1_3_max (lit : LiteratureTheorems.{u})
    {k n : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    ExactUniversalEdgeBound.{u} (k + 2) n (max (R k n) (J k n)) := by
  rw [← F_eq_max hn]
  exact theorem_1_3 lit hk hn

alias lemma_3_1 := cycle_pathFan_equivalence
alias construction_3_2_free := nearlyRegularGraph_pathFanFree
alias construction_3_2_count := nearlyRegularGraph_card_edgeFinset_eq_t
alias construction_3_3_free := splitGraph_pathFanFree
alias construction_3_3_count := splitGraph_card_edgeFinset_eq
alias remark_3_4 := sharp_threshold_identity
alias lemma_3_5 := linear_bound_real

theorem lemma_3_6 {k n : ℕ} (hk : 2 ≤ k)
    (hn : (5 * k + 2) / 2 ≤ n) :
    J k n = (k + 1) * (n - k - 1) := p_eq_terminal hk hn

theorem lemma_3_7 {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n) :
    F k n =
      if n ≤ Nat.floor (realCutoff k) then R k n
      else if n < (5 * k + 2) / 2 then (2 * n + (k + 1)) ^ 2 / 24
      else (k + 1) * (n - k - 1) := h_eq_piecewise_real hk hn

alias lemma_3_8 := merge_ineq_both
alias claim_3_1 := h_le_mul_sub_one_of_p_lt_h
alias lemma_3_9 := cycle_arithmetic_consequences
alias lemma_3_10 := small_c_arithmetic
alias theorem_4_1 := dirac_cycle_of_literature
alias theorem_4_2 := maNing_exterior_stability_of_literature
alias lemma_4_3 := exceptional_low_degree_or_W
alias lemma_4_4 := maNing_cycle_dichotomy
alias lemma_4_5 := closure_preserves_local_maximality_of_literature
alias lemma_4_6 := maNing_nonHamiltonianConnected_of_literature
alias lemma_4_7 := maNing_degree_of_literature
alias lemma_4_8_i := maNing_edge_bound_i_of_literature
alias lemma_4_8_ii := maNing_edge_bound_ii_of_literature
alias lemma_4_9 := maNing_strong_attachment_of_literature
alias lemma_4_10 := fanLvWang_switch_of_literature
alias lemma_4_11 := erdosGallai_path_of_literature
alias claim_4_1 := switching_terminal_claim_of_literature
alias lemma_5_1 := base_range_upper_of_literature
alias lemma_5_2 := terminal_bound_of_literature
alias lemma_5_3 := cycle_degree_on_cycle
alias lemma_5_4 := minimalCounterexample_setup
alias claim_5_1_i := claim_5_1_i_signed
alias claim_5_1_ii := h_eq_t_descends
alias claim_5_2 := ext_rich_host1_of_literature
alias claim_5_3 := ext_rich_host2
alias rich_case_halfCycle_mem_I := halfCycle_mem_A_of_large_outside_attachment

end Erdos767.FinalPaper
