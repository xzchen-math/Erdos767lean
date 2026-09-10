import Erdos767.RichCase
import Erdos767.ExceptionalCase

/-!
# The complete base-range proof

This file closes manuscript Lemma `lem:base` under the explicit Route-A
literature interface.  All case analysis after the cited inputs is proved in
Lean, including the exceptional `(k,n,c)=(3,8,6)` configuration.
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

local instance baseRangeDecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

/-- Manuscript Lemma `lem:base`: every `n`-vertex `PF_(k+2)`-free graph in
the base range has at most `h k n` edges.  The only assumptions are the
cited results packaged in `LiteratureTheorems`. -/
theorem base_range_upper_of_literature
    (lit : LiteratureTheorems.{u}) : BaseRangeUpper.{u} := by
  intro k n hk hn hnUpper
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instV instDec G instAdj hcard hfree
      by_contra hnotBound
      have hlarge : h k n + 1 ≤ G.edgeFinset.card := by omega
      obtain ⟨H, instHAdj, hHG, hedge⟩ :=
        exists_spanning_subgraph_edge_card_eq G hlarge
      have hfreeH : PathFanFree H (k + 2) := hfree.mono hHG
      have hIH : ∀ m : ℕ, k + 2 ≤ m → m < n →
          UniversalEdgeBound.{u} (k + 2) m (h k m) := by
        intro m hm hm_lt
        exact ih m hm_lt hm (by omega)
      obtain ⟨hedgeSetup, _hnonham, h2c, hmin, C,
          hlongest, hcycleLower, hcn⟩ :=
        minimalCounterexample_setup H lit hk hn hnUpper hcard hfreeH hedge hIH
      have hdich := maNing_cycle_dichotomy lit H C h2c
        hlongest.isLocallyMaximal (by simpa [hcard] using hcn)
      rcases hdich with
        ⟨s, S, hs2, hsUpper, hScard, hSdegree, hclique⟩ |
        ⟨R, hRcard, hRdegree⟩
      · have hsUpper' : s ≤ C.length / 2 - 1 := by
          simpa [C.card_vertexSubtype] using hsUpper
        have hbound := cycle_case_i_edge_bound lit hk hn hnUpper hcard
          hfreeH C h2c hlongest hcn hs2 hsUpper' hScard hSdegree hclique
        omega
      · have hRcard' : R.card = C.length / 2 - 1 := by
          simpa [C.card_vertexSubtype] using hRcard
        have hRdegree' : ∀ x ∈ R,
            (cycleCoreClosure C).degree x ≤ C.length / 2 := by
          simpa [C.card_vertexSubtype] using hRdegree
        by_cases hc9 : C.length ≤ 9
        · have hsmall := cycle_case_ii_small_edge_bound_or_exception lit hk hn
            hnUpper hcard hfreeH C h2c hlongest hcycleLower hcn hc9 R
            hRcard' hRdegree'
          rcases hsmall with hbound | ⟨hk3, hn8, hc6⟩
          · omega
          · subst k
            subst n
            have hedge17 : H.edgeFinset.card = 17 := by
              rw [hn8, small_c_exception_value.2] at hedgeSetup
              exact hedgeSetup
            have hinsideLe :
                (H.induce (↑C.vertexFinset : Set V)).edgeFinset.card ≤ 11 := by
              have hbound := cycle_case_ii_inside_bound hfreeH C R
                hRcard' hRdegree'
              norm_num [hc6] at hbound ⊢
              exact hbound
            have hextLe :
                (H.induce
                  (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
                  (edgesBetween H (Finset.univ \ C.vertexFinset)
                    C.vertexFinset).card ≤ 6 := by
              have hbound := maNing_edge_bound_ii_of_literature lit C h2c
                hlongest.isLocallyMaximal (by omega)
                (by simpa [hn8] using hcn)
              norm_num [hn8, hc6] at hbound ⊢
              exact hbound
            have hdecomp := edge_count_cycle_decomposition C
            have hinsideEq :
                (H.induce (↑C.vertexFinset : Set V)).edgeFinset.card = 11 := by
              change H.edgeFinset.card =
                (H.induce (↑C.vertexFinset : Set V)).edgeFinset.card +
                  ((H.induce
                    (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
                    (edgesBetween H (Finset.univ \ C.vertexFinset)
                      C.vertexFinset).card) at hdecomp
              omega
            have hminThree : ∀ x : V, 3 ≤ H.degree x := by
              intro x
              have hx := hmin.trans (H.minDegree_le_degree x)
              norm_num at hx ⊢
              exact hx
            have hcycleFour : ∀ (x : V) (hx : x ∈ C.vertexFinset),
                (H.induce (↑C.vertexFinset : Set V)).degree
                  ⟨x, hx⟩ ≤ 4 := by
              intro x hx
              simpa using cycle_degree_on_cycle hfreeH C x hx
            exact exceptional_case_contradiction H hn8 C hc6 hlongest
              hedge17 hinsideEq hminThree hcycleFour
        · have hc10 : 10 ≤ C.length := by omega
          let ext :=
            (H.induce
              (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
              (edgesBetween H (Finset.univ \ C.vertexFinset)
                C.vertexFinset).card
          by_cases hsparse :
              ext ≤ (C.length / 2 - 1) * (n - C.length)
          · have hsparseN :
                (H.induce
                  (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
                  (edgesBetween H (Finset.univ \ C.vertexFinset)
                    C.vertexFinset).card ≤
                    (C.length / 2 - 1) * (n - C.length) := by
              dsimp [ext] at hsparse
              exact hsparse
            have hbound := cycle_case_ii_sparse_edge_bound hk hn hnUpper
              hcard hfreeH C hcn R hRcard' hRdegree' hsparseN
            omega
          · have hrich :
                (C.length / 2 - 1) * (n - C.length) <
                  (H.induce
                    (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
                    (edgesBetween H (Finset.univ \ C.vertexFinset)
                      C.vertexFinset).card := by
              dsimp [ext] at hsparse
              omega
            have hbound := cycle_case_ii_rich_edge_bound lit hk hn hnUpper
              hcard hfreeH C h2c hlongest hcycleLower hcn hc10 hmin hrich
            omega

/-- Exact base-range conclusion, including the verified extremal
constructions from Chapter 3. -/
theorem exact_base_range_of_literature
    (lit : LiteratureTheorems.{u})
    {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2) :
    ExactUniversalEdgeBound.{u} (k + 2) n (h k n) :=
  exact_base_of_upper hk hn
    (base_range_upper_of_literature lit k n hk hn hnUpper)

/-- The complete `k ≥ 2` part of the manuscript's main theorem.  Unlike
`main_k_ge_two_of_baseRangeUpper`, this theorem has no unproved
paper-specific premise: it depends only on `LiteratureTheorems`. -/
theorem main_k_ge_two_of_literature
    (lit : LiteratureTheorems.{u})
    {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n) :
    if n < (5 * k + 2) / 2 then
      ExactUniversalEdgeBound.{u} (k + 2) n (h k n)
    else
      ExactUniversalEdgeBound.{u} (k + 2) n
        ((k + 1) * (n - k - 1)) :=
  main_k_ge_two_of_baseRangeUpper (base_range_upper_of_literature lit) hk hn

/-- Manuscript Lemma `lem:terminal`, now discharged directly from the
Route-A literature package via the verified base-range theorem. -/
theorem terminal_bound_of_literature
    (lit : LiteratureTheorems.{u})
    {k n : ℕ} (hk : 2 ≤ k) (hn : (5 * k + 2) / 2 ≤ n) :
    UniversalEdgeBound.{u} (k + 2) n
      ((k + 1) * (n - k - 1)) := by
  apply terminal_bound hk hn
  exact base_range_upper_of_literature lit k ((5 * k + 2) / 2)
    hk (by omega) le_rfl

/-- For `k = 1` and `n ≥ 4`, the comparison function is the Pósa value
`2n-4`. -/
theorem h_one_eq_two_mul_sub_four {n : ℕ} (hn : 4 ≤ n) :
    h 1 n = 2 * n - 4 := by
  rw [h_eq_max (by omega)]
  have ht : t 1 n = n := by simp [t]
  have hp : p 1 n = 2 * (n - 2) := by
    simp [p, A, splitTerm]
  rw [ht, hp, max_eq_right (by omega)]
  omega

/-- The manuscript's complete main theorem in the exact extremal-value
interface: for every `k ≥ 1` and `n ≥ k+2`, the maximum edge count is
`h k n`, the maximum of the two construction counts. -/
theorem main_theorem_of_literature
    (lit : LiteratureTheorems.{u})
    {k n : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    ExactUniversalEdgeBound.{u} (k + 2) n (h k n) := by
  rcases eq_or_lt_of_le hk with rfl | hkTwo
  · by_cases hnThree : n = 3
    · subst n
      have hh : h 1 3 = 3 := by decide
      rw [hh]
      exact exact_k_one_three
    · have hnFour : 4 ≤ n := by omega
      rw [h_one_eq_two_mul_sub_four hnFour]
      exact exact_k_one_of_four_le lit hnFour
  · have hmain := main_k_ge_two_of_literature lit hkTwo hn
    by_cases hsmall : n < (5 * k + 2) / 2
    · rw [if_pos hsmall] at hmain
      exact hmain
    · have hterminal : (5 * k + 2) / 2 ≤ n := by omega
      rw [h_eq_terminal hkTwo hterminal]
      rw [if_neg hsmall] at hmain
      exact hmain

end

end Erdos767
