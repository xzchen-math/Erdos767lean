import Erdos767.GraphSeparators
import Erdos767.MaNingEdges

/-!
# The base-range minimal counterexample setup

This file verifies the five structural conclusions collected in manuscript
Lemma `lem:minimal-counterexample-setup` (in a form parametrized by the
induction hypothesis for smaller orders).
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

local instance baseSetupDecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

/-- Path-fan freeness passes to a spanning subgraph. -/
theorem PathFanFree.mono {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {ell : ℕ} (hHG : H ≤ G) (hfree : PathFanFree G ell) :
    PathFanFree H ell := by
  rintro ⟨x, a, b, p, hp, hx, hcount⟩
  apply hfree
  let q : G.Walk a b := p.mapLe hHG
  refine ⟨x, a, b, q, ?_, ?_, ?_⟩
  · dsimp [q]
    exact hp.map Function.injective_id
  · rw [show q.support = p.support by
      exact SimpleGraph.Walk.support_mapLe_eq_support hHG p]
    exact hx
  · have hsubset : walkNeighbors x p ⊆ walkNeighbors x q := by
      intro y hy
      apply Finset.mem_filter.mpr
      have hyData := Finset.mem_filter.mp hy
      constructor
      · rw [show q.support = p.support by
          exact SimpleGraph.Walk.support_mapLe_eq_support hHG p]
        exact hyData.1
      · exact hHG hyData.2
    exact hcount.trans (Finset.card_le_card hsubset)

/-- A cycle has length at most the order of its graph. -/
theorem CycleWitness.length_le_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (C : CycleWitness G) :
    C.length ≤ Fintype.card V := by
  rw [← C.card_vertexFinset, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- Once a finite graph contains a cycle, it contains a longest cycle. -/
theorem exists_longestCycle_of_cycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C0 : CycleWitness G) :
    ∃ C : CycleWitness G, IsLongestCycle C := by
  classical
  let P : ℕ → Prop := fun m ↦ ∃ C : CycleWitness G, C.length = m
  let m := Nat.findGreatest P (Fintype.card V)
  have hP : P m := by
    apply Nat.findGreatest_spec (P := P) C0.length_le_card
    exact ⟨C0, rfl⟩
  obtain ⟨C, hCm⟩ := hP
  refine ⟨C, ?_⟩
  intro D
  rw [hCm]
  exact Nat.le_findGreatest D.length_le_card ⟨D, rfl⟩

/-- A cycle of full order is a Hamilton cycle. -/
theorem isHamiltonian_of_cycle_length_eq_card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) (hlen : C.length = Fintype.card V) :
    G.IsHamiltonian := by
  intro hcardOne
  exact ⟨C.base, C.walk,
    (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq).2
      ⟨C.isCycle, hlen⟩⟩

/-- Thin a graph to any prescribed number of its edges. -/
theorem exists_spanning_subgraph_edge_card_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : ℕ} (hB : B ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧ H.edgeFinset.card = B := by
  classical
  obtain ⟨E, hEG, hEcard⟩ := Finset.exists_subset_card_eq hB
  let D : Finset (Sym2 V) := G.edgeFinset \ E
  let H := G.deleteEdges (↑D : Set (Sym2 V))
  have hHE : H.edgeFinset = E := by
    dsimp [H]
    rw [SimpleGraph.edgeFinset_deleteEdges D]
    dsimp [D]
    exact Finset.sdiff_sdiff_eq_self hEG
  exact ⟨H, inferInstance, G.deleteEdges_le _, by rw [hHE, hEcard]⟩

/-- The verified data attached to an edge-minimal counterexample. -/
def MinimalCounterexampleSetup
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k n : ℕ) : Prop :=
  G.edgeFinset.card = h k n + 1 ∧
    ¬ G.IsHamiltonian ∧
    IsTwoConnected G ∧
    (k + 1) / 2 + 1 ≤ G.minDegree ∧
    ∃ C : CycleWitness G,
      IsLongestCycle C ∧
      2 * ((k + 1) / 2) + 2 ≤ C.length ∧
      C.length < n

/-- All five conclusions of the manuscript's minimal-counterexample setup,
assuming the base bound for every smaller admissible order. -/
theorem minimalCounterexample_setup
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (lit : LiteratureTheorems.{u}) {k n : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2)
    (hcard : Fintype.card V = n) (hfree : PathFanFree G (k + 2))
    (hedge : G.edgeFinset.card = h k n + 1)
    (hIH : ∀ m : ℕ, k + 2 ≤ m → m < n →
      UniversalEdgeBound.{u} (k + 2) m (h k m)) :
    MinimalCounterexampleSetup G k n := by
  classical
  have hnFour : 4 ≤ n := by omega
  have h2c : IsTwoConnected G := by
    by_contra hnot
    have hbound := edge_bound_of_not_twoConnected G hk hn hnUpper
      hcard hfree hIH hnot
    omega
  have hminVertex : ∀ v : V, (k + 1) / 2 + 1 ≤ G.degree v := by
    intro v
    let S : Set V := ({v} : Set V)ᶜ
    have hcardS : Fintype.card S = n - 1 := by
      change Fintype.card {x : V // x ≠ v} = n - 1
      rw [Fintype.card_subtype_compl (fun x : V ↦ x = v),
        Fintype.card_subtype_eq]
      omega
    have hfreeS : PathFanFree (G.induce S) (k + 2) :=
      pathFanFree_induce S hfree
    have hedgeS : (G.induce S).edgeFinset.card ≤ h k (n - 1) := by
      by_cases hsmall : n - 1 ≤ k + 1
      · have htriv := (G.induce S).card_edgeFinset_le_card_choose_two
        rw [hcardS] at htriv
        simpa [h, hsmall] using htriv
      · have hlarge : k + 2 ≤ n - 1 := by omega
        exact hIH (n - 1) hlarge (by omega) S (G.induce S)
          hcardS hfreeS
    have hdelete := card_edgeFinset_eq_induce_compl_singleton_add_degree
      (G := G) v
    change G.edgeFinset.card = (G.induce S).edgeFinset.card + G.degree v at hdelete
    have hinc := h_increment_lower hk hn
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
  have hmin : (k + 1) / 2 + 1 ≤ G.minDegree := by
    exact G.le_minDegree_of_forall_le_degree _ hminVertex
  have hnonham : ¬ G.IsHamiltonian := by
    intro hham
    haveI : Nontrivial V := ⟨Fintype.one_lt_card_iff.mp (by rw [hcard]; omega)⟩
    obtain ⟨p, hp⟩ := hham.exists_isHamiltonianCycle (Classical.choice inferInstance)
    let C : CycleWitness G := ⟨_, p, hp.isCycle⟩
    have hVC : C.vertexFinset = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      simpa [C, CycleWitness.vertexFinset] using hp.mem_support x
    have hdeg : ∀ x : V, G.degree x ≤ k + 1 := by
      intro x
      have hxC : x ∈ C.vertexFinset := by rw [hVC]; simp
      have hcdeg := cycle_degree_on_cycle hfree C x hxC
      have hmap :
          ((G.induce (↑C.vertexFinset : Set V)).neighborFinset
              ⟨x, hxC⟩).map
                (Function.Embedding.subtype (· ∈ C.vertexFinset)) =
            G.neighborFinset x ∩ C.vertexFinset := by
        ext y
        simp
      have hcardMap := congrArg Finset.card hmap
      rw [Finset.card_map] at hcardMap
      have hcardMap' :
          ((G.induce (↑C.vertexFinset : Set V)).neighborFinset
              ⟨x, hxC⟩).card =
            (G.neighborFinset x ∩ C.vertexFinset).card := by
        simpa using hcardMap
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc
        (G.neighborFinset x).card =
            (G.neighborFinset x ∩ C.vertexFinset).card := by
          rw [hVC]
          simp
        _ = ((G.induce (↑C.vertexFinset : Set V)).neighborFinset
              ⟨x, hxC⟩).card := hcardMap'.symm
        _ = (G.induce (↑C.vertexFinset : Set V)).degree ⟨x, hxC⟩ :=
          by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ k + 1 := hcdeg
    have hsum := Finset.sum_le_sum fun x (_hx : x ∈ Finset.univ) ↦ hdeg x
    have hhand := G.sum_degrees_eq_twice_card_edges
    have hsumConst : (∑ _x : V, (k + 1)) = (k + 1) * n := by
      simp [hcard, Nat.mul_comm]
    rw [hhand, hsumConst, hedge] at hsum
    have htLower := t_le_h (k := k) (n := n) hn
    unfold t at htLower
    omega
  obtain ⟨D, hDlower⟩ := lit.diracCycle G h2c
  obtain ⟨C, hClongest⟩ := exists_longestCycle_of_cycle D
  have hClt : C.length < n := by
    have hCle := C.length_le_card
    rw [hcard] at hCle
    by_contra hnotlt
    have hCeq : C.length = Fintype.card V := by omega
    exact hnonham (isHamiltonian_of_cycle_length_eq_card C hCeq)
  have hDiracNotN : ¬ n ≤ 2 * G.minDegree := by
    intro hnMin
    have hDge : n ≤ D.length := by
      have hminEq : min (Fintype.card V) (2 * G.minDegree) = n := by
        rw [hcard, min_eq_left hnMin]
      simpa [hminEq] using hDlower
    have hDle := D.length_le_card
    have hDeq : D.length = Fintype.card V := by omega
    exact hnonham (isHamiltonian_of_cycle_length_eq_card D hDeq)
  have hDdegree : 2 * G.minDegree ≤ D.length := by
    have hminEq : min (Fintype.card V) (2 * G.minDegree) =
        2 * G.minDegree := by
      rw [min_eq_right]
      rw [hcard]
      omega
    simpa [hminEq] using hDlower
  have hDleC := hClongest D
  have hcycleLower : 2 * ((k + 1) / 2) + 2 ≤ C.length := by
    nlinarith
  exact ⟨hedge, hnonham, h2c, hmin, C, hClongest, hcycleLower, hClt⟩

end

end Erdos767
