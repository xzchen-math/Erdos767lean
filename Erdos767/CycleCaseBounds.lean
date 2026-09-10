import Erdos767.BaseSetup

/-!
# Edge bounds in the two Ma--Ning cycle cases
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

local instance cycleCaseDecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

/-- Degree summation on the cycle, with a distinguished set of vertices
having the sharper degree bound `a`. -/
theorem induced_cycle_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k a : ℕ} (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G)
    (R : Finset {x // x ∈ C.vertexFinset})
    (hRdegree : ∀ x ∈ R,
      (G.induce (↑C.vertexFinset : Set V)).degree x ≤ a) :
    (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card ≤
      (R.card * a + (C.length - R.card) * (k + 1)) / 2 := by
  classical
  let H := G.induce (↑C.vertexFinset : Set V)
  have hAll : ∀ x : {x // x ∈ C.vertexFinset}, H.degree x ≤ k + 1 := by
    intro x
    exact cycle_degree_on_cycle hfree C x x.property
  have hsumR : (∑ x ∈ R, H.degree x) ≤ R.card * a := by
    simpa [Nat.mul_comm] using R.sum_le_card_nsmul (fun x ↦ H.degree x) a hRdegree
  have hsumComp : (∑ x ∈ Rᶜ, H.degree x) ≤ Rᶜ.card * (k + 1) := by
    apply Rᶜ.sum_le_card_nsmul
    intro x hx
    exact hAll x
  have hcardComp : Rᶜ.card = C.length - R.card := by
    rw [Finset.card_compl, C.card_vertexSubtype]
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hdouble : 2 * H.edgeFinset.card ≤
      R.card * a + (C.length - R.card) * (k + 1) := by
    rw [hcardComp] at hsumComp
    calc
      2 * H.edgeFinset.card = ∑ x, H.degree x := hsum.symm
      _ = (∑ x ∈ R, H.degree x) + (∑ x ∈ Rᶜ, H.degree x) := by
        simpa using (R.sum_add_sum_compl (fun x ↦ H.degree x)).symm
      _ ≤ R.card * a + (C.length - R.card) * (k + 1) :=
        Nat.add_le_add hsumR hsumComp
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  simpa [Nat.mul_comm] using hdouble

/-- Map a finset of the cycle-vertex subtype back to the ambient vertex
type, preserving cardinality. -/
def ambientCycleFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) (R : Finset {x // x ∈ C.vertexFinset}) : Finset V :=
  R.map (Function.Embedding.subtype (· ∈ C.vertexFinset))

theorem ambientCycleFinset_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) (R : Finset {x // x ∈ C.vertexFinset}) :
    (ambientCycleFinset C R).card = R.card := by
  simp [ambientCycleFinset]

theorem ambientCycleFinset_subset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) (R : Finset {x // x ∈ C.vertexFinset}) :
    ambientCycleFinset C R ⊆ C.vertexFinset := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  exact y.property

/-- A clique in the closed cycle core becomes the corresponding clique in
the full `C`-closure. -/
theorem cycleClosure_clique_of_core_compl_clique
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G)
    (R : Finset {x // x ∈ C.vertexFinset})
    (hclique : (cycleCoreClosure C).IsClique
      (↑(Finset.univ \ R) : Set {x // x ∈ C.vertexFinset})) :
    (cycleClosure C).IsClique
      (↑(C.vertexFinset \ ambientCycleFinset C R) : Set V) := by
  classical
  rw [SimpleGraph.isClique_iff]
  intro a ha b hb hab
  have haData := Finset.mem_sdiff.mp ha
  have hbData := Finset.mem_sdiff.mp hb
  let aa : {x // x ∈ C.vertexFinset} := ⟨a, haData.1⟩
  let bb : {x // x ∈ C.vertexFinset} := ⟨b, hbData.1⟩
  have haa : aa ∈ Finset.univ \ R := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro haaR
    apply haData.2
    exact Finset.mem_map.mpr ⟨aa, haaR, rfl⟩
  have hbb : bb ∈ Finset.univ \ R := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hbbR
    apply hbData.2
    exact Finset.mem_map.mpr ⟨bb, hbbR, rfl⟩
  have habCore := (SimpleGraph.isClique_iff (cycleCoreClosure C)).mp
    hclique haa hbb (by simpa [aa, bb] using hab)
  change ((cycleClosure C).induce
    (↑C.vertexFinset : Set V)).Adj aa bb
  rw [cycleClosure_induce_cycle_eq]
  exact habCore

/-- The first side of the Ma--Ning degree/clique dichotomy gives the desired
base-range edge bound. -/
theorem cycle_case_i_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (lit : LiteratureTheorems.{u}) {k n : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2)
    (hcard : Fintype.card V = n) (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G) (h2c : IsTwoConnected G)
    (hlongest : IsLongestCycle C) (hcn : C.length < n)
    {s : ℕ} {R : Finset {x // x ∈ C.vertexFinset}}
    (hs2 : 2 ≤ s) (hsUpper : s ≤ C.length / 2 - 1)
    (hRcard : R.card = s - 1)
    (hRdegree : ∀ x ∈ R, (cycleCoreClosure C).degree x ≤ s)
    (hclique : (cycleCoreClosure C).IsClique
      (↑(Finset.univ \ R) : Set {x // x ∈ C.vertexFinset})) :
    G.edgeFinset.card ≤ h k n := by
  classical
  have hloc := hlongest.isLocallyMaximal
  let S := ambientCycleFinset C R
  have hSsub : S ⊆ C.vertexFinset := ambientCycleFinset_subset C R
  have hScard : S.card = s - 1 := by
    rw [ambientCycleFinset_card, hRcard]
  have hCliqueClosure := cycleClosure_clique_of_core_compl_clique C R hclique
  have hext := maNing_edge_bound_i_of_literature lit C h2c hloc
    (by simpa [hcard] using hcn) s hs2 hsUpper S hSsub hScard hCliqueClosure
  have hRdegreeG : ∀ x ∈ R,
      (G.induce (↑C.vertexFinset : Set V)).degree x ≤ s := by
    intro x hx
    exact ((G.induce (↑C.vertexFinset : Set V)).degree_le_of_le
      (induceCycle_le_cycleCoreClosure C)).trans (hRdegree x hx)
  have hinside := induced_cycle_edge_bound hfree C R hRdegreeG
  rw [hRcard] at hinside
  have hsLen : s ≤ C.length := by omega
  have hsub : C.length - (s - 1) = C.length - s + 1 := by omega
  rw [hsub] at hinside
  have harith := cycle_arithmetic_consequence_i hk hn hnUpper hcn hs2 hsUpper
  rw [hcard] at hext
  have hsum := Nat.add_le_add_right hinside (s * (n - C.length))
  exact hext.trans (hsum.trans (by simpa [Nat.add_comm] using harith))

/-- The common degree estimate in the second Ma--Ning alternative. -/
theorem cycle_case_ii_inside_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G)
    (R : Finset {x // x ∈ C.vertexFinset})
    (hRcard : R.card = C.length / 2 - 1)
    (hRdegree : ∀ x ∈ R,
      (cycleCoreClosure C).degree x ≤ C.length / 2) :
    (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card ≤
      (((C.length / 2 - 1) * min (C.length / 2) (k + 1) +
        (C.length - C.length / 2 + 1) * (k + 1))) / 2 := by
  have hRdegreeG : ∀ x ∈ R,
      (G.induce (↑C.vertexFinset : Set V)).degree x ≤
        min (C.length / 2) (k + 1) := by
    intro x hx
    apply le_min
    · exact ((G.induce (↑C.vertexFinset : Set V)).degree_le_of_le
        (induceCycle_le_cycleCoreClosure C)).trans (hRdegree x hx)
    · exact cycle_degree_on_cycle hfree C x x.property
  have hbound := induced_cycle_edge_bound hfree C R hRdegreeG
  rw [hRcard] at hbound
  have hqpos : 1 ≤ C.length / 2 := by
    have := C.isCycle.three_le_length
    change 3 ≤ C.length at this
    omega
  have hsub : C.length - (C.length / 2 - 1) =
      C.length - C.length / 2 + 1 := by omega
  simpa [hsub] using hbound

/-- In alternative (ii), the sparse-exterior subcase is bounded by the
second cycle arithmetic consequence. -/
theorem cycle_case_ii_sparse_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2)
    (hcard : Fintype.card V = n) (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G) (hcn : C.length < n)
    (R : Finset {x // x ∈ C.vertexFinset})
    (hRcard : R.card = C.length / 2 - 1)
    (hRdegree : ∀ x ∈ R,
      (cycleCoreClosure C).degree x ≤ C.length / 2)
    (hsparse :
      (G.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
        (edgesBetween G (Finset.univ \ C.vertexFinset)
          C.vertexFinset).card ≤
      (C.length / 2 - 1) * (n - C.length)) :
    G.edgeFinset.card ≤ h k n := by
  have hinside := cycle_case_ii_inside_bound hfree C R hRcard hRdegree
  have hdec := edge_count_cycle_decomposition C
  rw [hdec]
  have hsum := Nat.add_le_add hinside hsparse
  have harith := cycle_arithmetic_consequence_ii hk hn hnUpper hcn
    (by
      have hc3 := C.isCycle.three_le_length
      change 3 ≤ C.length at hc3
      omega)
  exact hsum.trans (by simpa [Nat.add_comm] using harith)

/-- For cycles of length at most nine, alternative (ii) gives the desired
bound except for the single numerical triple isolated in the manuscript. -/
theorem cycle_case_ii_small_edge_bound_or_exception
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (lit : LiteratureTheorems.{u}) {k n : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2)
    (hcard : Fintype.card V = n) (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G) (h2c : IsTwoConnected G)
    (hlongest : IsLongestCycle C)
    (hcycleLower : 2 * ((k + 1) / 2) + 2 ≤ C.length)
    (hcn : C.length < n) (hc9 : C.length ≤ 9)
    (R : Finset {x // x ∈ C.vertexFinset})
    (hRcard : R.card = C.length / 2 - 1)
    (hRdegree : ∀ x ∈ R,
      (cycleCoreClosure C).degree x ≤ C.length / 2) :
    G.edgeFinset.card ≤ h k n ∨
      (k = 3 ∧ n = 8 ∧ C.length = 6) := by
  classical
  by_cases hex : k = 3 ∧ n = 8 ∧ C.length = 6
  · exact Or.inr hex
  left
  have hk6 : k ≤ 6 := by omega
  have hqk : C.length / 2 ≤ k + 1 := by omega
  have hc4 : 4 ≤ C.length := by omega
  have hext := maNing_edge_bound_ii_of_literature lit C h2c
    hlongest.isLocallyMaximal hc4 (by simpa [hcard] using hcn)
  rw [hcard] at hext
  have hinside := cycle_case_ii_inside_bound hfree C R hRcard hRdegree
  rw [min_eq_left hqk] at hinside
  have hdec := edge_count_cycle_decomposition C
  rw [hdec]
  have hsum := Nat.add_le_add hinside hext
  have harith := small_c_arithmetic hk hk6 hn hnUpper hcycleLower hcn hc9 hex
  exact hsum.trans (by simpa [Nat.add_comm] using harith)

end

end Erdos767
