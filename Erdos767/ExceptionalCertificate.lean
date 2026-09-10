import Erdos767.FinsetEdgeDecomposition

/-!
# Paper proof of the exceptional `(3,8,6)` configuration

This module formalizes the manuscript's combinatorial classification argument.
It contains no Boolean adjacency-matrix search or compiler-reflection
certificate: Lean checks the successive neighborhood classifications, the
explicit seven- and eight-cycles, and the final chord-incidence count as
separate lemmas.
-/

namespace Erdos767

open SimpleGraph

noncomputable section

def sixSet : Finset (Fin 8) := Finset.univ.filter fun x ↦ x.1 < 6

def nextFin (m : ℕ) [NeZero m] (i : Fin m) : Fin m :=
  ⟨(i.1 + 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩

def GraphHasCycleEmbedding (K : SimpleGraph (Fin 8)) (m : ℕ)
    [NeZero m] : Prop :=
  ∃ f : Fin m ↪ Fin 8, ∀ i : Fin m, K.Adj (f i) (f (nextFin m i))

set_option maxRecDepth 100000 in
theorem fin8_filter_card_eq_bool_sum (f : Fin 8 → Bool) :
    (Finset.univ.filter fun x ↦ f x = true).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat +
      (f 4).toNat + (f 5).toNat + (f 6).toNat + (f 7).toNat := by
  decide +revert

set_option maxRecDepth 100000 in
theorem six_filter_card_eq_bool_sum (f : Fin 8 → Bool) :
    (sixSet.filter fun x ↦ f x = true).card =
      (f 0).toNat + (f 1).toNat + (f 2).toNat +
      (f 3).toNat + (f 4).toNat + (f 5).toNat := by
  decide +revert

theorem induce_six_degree_eq_filter_card
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (x : Fin 8) (hx : x ∈ sixSet) :
    (K.induce (↑sixSet : Set (Fin 8))).degree ⟨x, hx⟩ =
      (sixSet.filter fun y ↦ K.Adj x y).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap :
      ((K.induce (↑sixSet : Set (Fin 8))).neighborFinset ⟨x, hx⟩).map
          (Function.Embedding.subtype (· ∈ sixSet)) =
        sixSet.filter fun y ↦ K.Adj x y := by
    ext y
    simp [and_comm]
  have := congrArg Finset.card hmap
  simpa using this

def cycleNeighbors (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (x : Fin 8) : Finset (Fin 8) :=
  sixSet.filter fun y ↦ K.Adj x y

theorem adj_of_mem_cycleNeighbors
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    {x y : Fin 8} (hy : y ∈ cycleNeighbors K x) : K.Adj x y :=
  (Finset.mem_filter.mp hy).2

theorem outside_sixSet :
    (Finset.univ \ sixSet : Finset (Fin 8)) = {6, 7} := by
  decide

theorem degree_six_eq_cycleNeighbors_add
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj] :
    K.degree 6 = (cycleNeighbors K 6).card +
      if K.Adj 6 7 then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h8 := fin8_filter_card_eq_bool_sum
    (fun y ↦ decide (K.Adj 6 y))
  have h6 := six_filter_card_eq_bool_sum
    (fun y ↦ decide (K.Adj 6 y))
  simp only [decide_eq_true_eq] at h8 h6
  have hn : K.neighborFinset 6 =
      Finset.univ.filter fun y ↦ K.Adj 6 y := by
    ext y
    simp
  rw [hn, h8]
  change _ = (sixSet.filter fun y ↦ K.Adj 6 y).card + _
  rw [h6]
  by_cases h67 : K.Adj 6 7
  · simp [h67, K.loopless]
  · simp [h67, K.loopless]

theorem degree_seven_eq_cycleNeighbors_add
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj] :
    K.degree 7 = (cycleNeighbors K 7).card +
      if K.Adj 6 7 then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h8 := fin8_filter_card_eq_bool_sum
    (fun y ↦ decide (K.Adj 7 y))
  have h6 := six_filter_card_eq_bool_sum
    (fun y ↦ decide (K.Adj 7 y))
  simp only [decide_eq_true_eq] at h8 h6
  have hn : K.neighborFinset 7 =
      Finset.univ.filter fun y ↦ K.Adj 7 y := by
    ext y
    simp
  rw [hn, h8]
  change _ = (sixSet.filter fun y ↦ K.Adj 7 y).card + _
  rw [h6]
  by_cases h67 : K.Adj 6 7
  · simp [h67, K.loopless, K.adj_comm]
  · simp [h67, K.loopless, K.adj_comm]

theorem crossing_sixSet_card_eq_cycleNeighbors_add
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj] :
    (edgesBetween K (Finset.univ \ sixSet) sixSet).card =
      (cycleNeighbors K 6).card + (cycleNeighbors K 7).card := by
  have hdisj : Disjoint (Finset.univ \ sixSet) sixSet := by
    apply Finset.disjoint_left.mpr
    intro x hx hxsix
    exact (Finset.mem_sdiff.mp hx).2 hxsix
  rw [edgesBetween_card_eq_sum_neighborsIn _ _ hdisj]
  rw [outside_sixSet]
  simp [neighborsIn, cycleNeighbors]

theorem outside_sixSet_edge_card
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj] :
    (K.induce
      (↑(Finset.univ \ sixSet) : Set (Fin 8))).edgeFinset.card =
        if K.Adj 6 7 then 1 else 0 := by
  classical
  by_cases h67 : K.Adj 6 7
  · rw [if_pos h67]
    let x6 : ↥(↑(Finset.univ \ sixSet) : Set (Fin 8)) :=
      ⟨6, by simp [outside_sixSet]⟩
    let x7 : ↥(↑(Finset.univ \ sixSet) : Set (Fin 8)) :=
      ⟨7, by simp [outside_sixSet]⟩
    have hedge : s(x6, x7) ∈
        (K.induce
          (↑(Finset.univ \ sixSet) : Set (Fin 8))).edgeFinset := by
      simp [x6, x7, h67]
    have hlower : 1 ≤
        (K.induce
          (↑(Finset.univ \ sixSet) : Set (Fin 8))).edgeFinset.card :=
      Finset.one_le_card.mpr ⟨s(x6, x7), hedge⟩
    have hupper :=
      (K.induce
        (↑(Finset.univ \ sixSet) : Set (Fin 8))).card_edgeFinset_le_card_choose_two
    have hverts : Fintype.card
        ↥(↑(Finset.univ \ sixSet) : Set (Fin 8)) = 2 := by
      simpa [outside_sixSet]
    rw [hverts] at hupper
    norm_num at hupper
    omega
  · rw [if_neg h67, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset] at he
        have hxy : K.Adj x.1 y.1 := he
        have hx : x.1 = 6 ∨ x.1 = 7 := by
          have hxmem : x.1 ∈ ({6, 7} : Finset (Fin 8)) := by
            rw [← outside_sixSet]
            exact x.2
          simpa using hxmem
        have hy : y.1 = 6 ∨ y.1 = 7 := by
          have hymem : y.1 ∈ ({6, 7} : Finset (Fin 8)) := by
            rw [← outside_sixSet]
            exact y.2
          simpa using hymem
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact K.loopless.irrefl _ (hx ▸ hy ▸ hxy)
        · exact h67 (hx ▸ hy ▸ hxy)
        · exact h67 ((hx ▸ hy ▸ hxy).symm)
        · exact K.loopless.irrefl _ (hx ▸ hy ▸ hxy)

def evenCycleTriple : Finset (Fin 8) := {0, 2, 4}

def oddCycleTriple : Finset (Fin 8) := {1, 3, 5}

def NoConsecutiveCyclePair (A : Finset (Fin 8)) : Prop :=
  ¬(0 ∈ A ∧ 1 ∈ A) ∧ ¬(1 ∈ A ∧ 2 ∈ A) ∧
  ¬(2 ∈ A ∧ 3 ∈ A) ∧ ¬(3 ∈ A ∧ 4 ∈ A) ∧
  ¬(4 ∈ A ∧ 5 ∈ A) ∧ ¬(5 ∈ A ∧ 0 ∈ A)

def BoolNoConsecutiveCyclePair (f : Fin 8 → Bool) : Prop :=
  ¬(f 0 = true ∧ f 1 = true) ∧ ¬(f 1 = true ∧ f 2 = true) ∧
  ¬(f 2 = true ∧ f 3 = true) ∧ ¬(f 3 = true ∧ f 4 = true) ∧
  ¬(f 4 = true ∧ f 5 = true) ∧ ¬(f 5 = true ∧ f 0 = true)

theorem bool_independent_cycle_triple_classification (f : Fin 8 → Bool)
    (hcard : (f 0).toNat + (f 1).toNat + (f 2).toNat +
      (f 3).toNat + (f 4).toNat + (f 5).toNat = 3)
    (hind : BoolNoConsecutiveCyclePair f) :
    (f 0 = true ∧ f 1 = false ∧ f 2 = true ∧
      f 3 = false ∧ f 4 = true ∧ f 5 = false) ∨
    (f 0 = false ∧ f 1 = true ∧ f 2 = false ∧
      f 3 = true ∧ f 4 = false ∧ f 5 = true) := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;>
    cases h3 : f 3 <;> cases h4 : f 4 <;> cases h5 : f 5 <;>
    simp_all [BoolNoConsecutiveCyclePair] <;> omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem independent_cycle_triple_classification (A : Finset (Fin 8))
    (hsub : A ⊆ sixSet) (hcard : A.card = 3)
    (hind : NoConsecutiveCyclePair A) :
    A = evenCycleTriple ∨ A = oddCycleTriple := by
  let f : Fin 8 → Bool := fun x ↦ decide (x ∈ A)
  have hcount := six_filter_card_eq_bool_sum f
  have hfilter : (sixSet.filter fun x ↦ f x = true) = A := by
    ext x
    simp only [Finset.mem_filter]
    dsimp [f]
    simp only [decide_eq_true_eq]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hsub hx, hx⟩⟩
  rw [hfilter, hcard] at hcount
  have hindB : BoolNoConsecutiveCyclePair f := by
    simpa [BoolNoConsecutiveCyclePair, NoConsecutiveCyclePair, f] using hind
  have hpattern := bool_independent_cycle_triple_classification f hcount.symm hindB
  have h6 : (6 : Fin 8) ∉ A := fun h ↦ by
    have := hsub h
    simp [sixSet] at this
  have h7 : (7 : Fin 8) ∉ A := fun h ↦ by
    have := hsub h
    simp [sixSet] at this
  rcases hpattern with ⟨hf0, hf1, hf2, hf3, hf4, hf5⟩ |
      ⟨hf0, hf1, hf2, hf3, hf4, hf5⟩
  · have h0 : (0 : Fin 8) ∈ A := by simpa [f] using hf0
    have h1 : (1 : Fin 8) ∉ A := by simpa [f] using hf1
    have h2 : (2 : Fin 8) ∈ A := by simpa [f] using hf2
    have h3 : (3 : Fin 8) ∉ A := by simpa [f] using hf3
    have h4 : (4 : Fin 8) ∈ A := by simpa [f] using hf4
    have h5 : (5 : Fin 8) ∉ A := by simpa [f] using hf5
    left
    ext x
    fin_cases x <;> simp [evenCycleTriple, h0, h1, h2, h3, h4, h5, h6, h7]
  · have h0 : (0 : Fin 8) ∉ A := by simpa [f] using hf0
    have h1 : (1 : Fin 8) ∈ A := by simpa [f] using hf1
    have h2 : (2 : Fin 8) ∉ A := by simpa [f] using hf2
    have h3 : (3 : Fin 8) ∈ A := by simpa [f] using hf3
    have h4 : (4 : Fin 8) ∉ A := by simpa [f] using hf4
    have h5 : (5 : Fin 8) ∈ A := by simpa [f] using hf5
    right
    ext x
    fin_cases x <;> simp [oddCycleTriple, h0, h1, h2, h3, h4, h5, h6, h7]

def HasShortOrientedPair (A B : Finset (Fin 8)) : Prop :=
  ((0 ∈ A ∧ 1 ∈ B) ∨ (1 ∈ A ∧ 0 ∈ B)) ∨
  ((1 ∈ A ∧ 2 ∈ B) ∨ (2 ∈ A ∧ 1 ∈ B)) ∨
  ((2 ∈ A ∧ 3 ∈ B) ∨ (3 ∈ A ∧ 2 ∈ B)) ∨
  ((3 ∈ A ∧ 4 ∈ B) ∨ (4 ∈ A ∧ 3 ∈ B)) ∨
  ((4 ∈ A ∧ 5 ∈ B) ∨ (5 ∈ A ∧ 4 ∈ B)) ∨
  ((5 ∈ A ∧ 0 ∈ B) ∨ (0 ∈ A ∧ 5 ∈ B)) ∨
  ((0 ∈ A ∧ 2 ∈ B) ∨ (2 ∈ A ∧ 0 ∈ B)) ∨
  ((1 ∈ A ∧ 3 ∈ B) ∨ (3 ∈ A ∧ 1 ∈ B)) ∨
  ((2 ∈ A ∧ 4 ∈ B) ∨ (4 ∈ A ∧ 2 ∈ B)) ∨
  ((3 ∈ A ∧ 5 ∈ B) ∨ (5 ∈ A ∧ 3 ∈ B)) ∨
  ((4 ∈ A ∧ 0 ∈ B) ∨ (0 ∈ A ∧ 4 ∈ B)) ∨
  ((5 ∈ A ∧ 1 ∈ B) ∨ (1 ∈ A ∧ 5 ∈ B))

theorem HasShortOrientedPair.swap {A B : Finset (Fin 8)}
    (h : HasShortOrientedPair A B) : HasShortOrientedPair B A := by
  simpa [HasShortOrientedPair, and_comm, or_comm] using h

def cycleOpposite (x : Fin 8) : Fin 8 :=
  match x.1 with
  | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 0
  | 4 => 1 | 5 => 2 | _ => x

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem short_oriented_pair_of_card_three_two
    (A B : Finset (Fin 8)) (hAsub : A ⊆ sixSet)
    (hBsub : B ⊆ sixSet) (hAcard : A.card = 3) (hBcard : 2 ≤ B.card) :
    HasShortOrientedPair A B := by
  have hBpos : 0 < B.card := by omega
  obtain ⟨y, hyB⟩ := Finset.card_pos.mp hBpos
  have hySix := hBsub hyB
  by_contra hshort
  have hsubTwo : A ⊆ ({y, cycleOpposite y} : Finset (Fin 8)) := by
    intro x hx
    have hxSix := hAsub hx
    fin_cases y <;> fin_cases x <;>
      simp_all [HasShortOrientedPair, cycleOpposite, sixSet]
  have hle := Finset.card_le_card hsubTwo
  have hpairCard : ({y, cycleOpposite y} : Finset (Fin 8)).card = 2 := by
    fin_cases y <;> simp [cycleOpposite] <;> simp [sixSet] at hySix
  rw [hpairCard, hAcard] at hle
  omega

abbrev DistinctFin7 (a b c d e f g : Fin 8) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ a ≠ g ∧
  b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧
  c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ c ≠ g ∧
  d ≠ e ∧ d ≠ f ∧ d ≠ g ∧ e ≠ f ∧ e ≠ g ∧ f ≠ g

theorem graphHasCycleEmbedding7_of
    (K : SimpleGraph (Fin 8))
    {a b c d e f g : Fin 8}
    (hd : DistinctFin7 a b c d e f g)
    (hab : K.Adj a b) (hbc : K.Adj b c) (hcd : K.Adj c d)
    (hde : K.Adj d e) (hef : K.Adj e f) (hfg : K.Adj f g)
    (hga : K.Adj g a) : GraphHasCycleEmbedding K 7 := by
  rcases hd with
    ⟨habn, hacn, hadn, haen, hafn, hagn,
      hbcn, hbdn, hben, hbfn, hbgn,
      hcdn, hcen, hcfn, hcgn,
      hden, hdfn, hdgn, hefn, hegn, hfgn⟩
  let φ : Fin 7 → Fin 8 := fun i ↦ match i.1 with
    | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g
  have hφ : Function.Injective φ := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [φ] <;> aesop
  exact ⟨⟨φ, hφ⟩, by
    intro i
    fin_cases i <;> simp [φ, nextFin] <;> aesop⟩

abbrev DistinctFin8 (a b c d e f g h : Fin 8) : Prop :=
  DistinctFin7 a b c d e f g ∧
  a ≠ h ∧ b ≠ h ∧ c ≠ h ∧ d ≠ h ∧ e ≠ h ∧ f ≠ h ∧ g ≠ h

theorem graphHasCycleEmbedding8_of
    (K : SimpleGraph (Fin 8))
    {a b c d e f g h : Fin 8}
    (hd : DistinctFin8 a b c d e f g h)
    (hab : K.Adj a b) (hbc : K.Adj b c) (hcd : K.Adj c d)
    (hde : K.Adj d e) (hef : K.Adj e f) (hfg : K.Adj f g)
    (hgh : K.Adj g h) (hha : K.Adj h a) :
    GraphHasCycleEmbedding K 8 := by
  rcases hd with
    ⟨⟨habn, hacn, hadn, haen, hafn, hagn,
        hbcn, hbdn, hben, hbfn, hbgn,
        hcdn, hcen, hcfn, hcgn,
        hden, hdfn, hdgn, hefn, hegn, hfgn⟩,
      hahn, hbhn, hchn, hdhn, hehn, hfhn, hghn⟩
  let φ : Fin 8 → Fin 8 := fun i ↦ match i.1 with
    | 0 => a | 1 => b | 2 => c | 3 => d
    | 4 => e | 5 => f | 6 => g | _ => h
  have hφ : Function.Injective φ := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [φ] <;> aesop
  exact ⟨⟨φ, hφ⟩, by
    intro i
    fin_cases i <;> simp [φ, nextFin] <;> aesop⟩

/-- The paper's “distance at most two” step.  The path through the two
adjacent exterior vertices replaces the shorter arc of the canonical
six-cycle and produces a seven- or eight-cycle. -/
theorem long_cycle_of_adjacent_outside_short_pair
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (h67 : K.Adj 6 7)
    (hshort : HasShortOrientedPair
      (cycleNeighbors K 6) (cycleNeighbors K 7)) :
    GraphHasCycleEmbedding K 7 ∨ GraphHasCycleEmbedding K 8 := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  simp [HasShortOrientedPair, cycleNeighbors, sixSet] at hshort
  rcases hshort with h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨h60, h71⟩ | ⟨h61, h70⟩
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h71 h12 h23 h34 h45 h50 h60.symm
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h70 h50.symm h45.symm h34.symm h23.symm h12.symm h61.symm
  · rcases h with ⟨h61, h72⟩ | ⟨h62, h71⟩
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h72 h23 h34 h45 h50 h01 h61.symm
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h71 h01.symm h50.symm h45.symm h34.symm h23.symm h62.symm
  · rcases h with ⟨h62, h73⟩ | ⟨h63, h72⟩
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h73 h34 h45 h50 h01 h12 h62.symm
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h72 h12.symm h01.symm h50.symm h45.symm h34.symm h63.symm
  · rcases h with ⟨h63, h74⟩ | ⟨h64, h73⟩
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h74 h45 h50 h01 h12 h23 h63.symm
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h73 h23.symm h12.symm h01.symm h50.symm h45.symm h64.symm
  · rcases h with ⟨h64, h75⟩ | ⟨h65, h74⟩
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h75 h50 h01 h12 h23 h34 h64.symm
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h74 h34.symm h23.symm h12.symm h01.symm h50.symm h65.symm
  · rcases h with ⟨h65, h70⟩ | ⟨h60, h75⟩
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h70 h01 h12 h23 h34 h45 h65.symm
    · right
      exact graphHasCycleEmbedding8_of K (by decide)
        h67 h75 h45.symm h34.symm h23.symm h12.symm h01.symm h60.symm
  · rcases h with ⟨h60, h72⟩ | ⟨h62, h70⟩
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h72 h23 h34 h45 h50 h60.symm
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h70 h50.symm h45.symm h34.symm h23.symm h62.symm
  · rcases h with ⟨h61, h73⟩ | ⟨h63, h71⟩
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h73 h34 h45 h50 h01 h61.symm
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h71 h01.symm h50.symm h45.symm h34.symm h63.symm
  · rcases h with ⟨h62, h74⟩ | ⟨h64, h72⟩
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h74 h45 h50 h01 h12 h62.symm
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h72 h12.symm h01.symm h50.symm h45.symm h64.symm
  · rcases h with ⟨h63, h75⟩ | ⟨h65, h73⟩
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h75 h50 h01 h12 h23 h63.symm
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h73 h23.symm h12.symm h01.symm h50.symm h65.symm
  · rcases h with ⟨h64, h70⟩ | ⟨h60, h74⟩
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h70 h01 h12 h23 h34 h64.symm
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h74 h34.symm h23.symm h12.symm h01.symm h60.symm
  · rcases h with ⟨h65, h71⟩ | ⟨h61, h75⟩
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h71 h12 h23 h34 h45 h65.symm
    · left
      exact graphHasCycleEmbedding7_of K (by decide)
        h67 h75 h45.symm h34.symm h23.symm h12.symm h61.symm

/-- If an exterior vertex met two consecutive vertices of the canonical
six-cycle, replacing that cycle edge by the exterior vertex would give the
forbidden seven-cycle.  This is the next classification step in the paper. -/
theorem no_consecutive_cycle_neighbors
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hno7 : ¬ GraphHasCycleEmbedding K 7) :
    NoConsecutiveCyclePair (cycleNeighbors K 6) ∧
      NoConsecutiveCyclePair (cycleNeighbors K 7) := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  have hsix : NoConsecutiveCyclePair (cycleNeighbors K 6) := by
    simp only [NoConsecutiveCyclePair, cycleNeighbors,
      Finset.mem_filter]
    simp only [show (0 : Fin 8) ∈ sixSet by decide,
      show (1 : Fin 8) ∈ sixSet by decide,
      show (2 : Fin 8) ∈ sixSet by decide,
      show (3 : Fin 8) ∈ sixSet by decide,
      show (4 : Fin 8) ∈ sixSet by decide,
      show (5 : Fin 8) ∈ sixSet by decide, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨h60, h61⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h60 h50.symm h45.symm h34.symm h23.symm h12.symm h61.symm)
    · rintro ⟨h61, h62⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h61 h01.symm h50.symm h45.symm h34.symm h23.symm h62.symm)
    · rintro ⟨h62, h63⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h62 h12.symm h01.symm h50.symm h45.symm h34.symm h63.symm)
    · rintro ⟨h63, h64⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h63 h23.symm h12.symm h01.symm h50.symm h45.symm h64.symm)
    · rintro ⟨h64, h65⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h64 h34.symm h23.symm h12.symm h01.symm h50.symm h65.symm)
    · rintro ⟨h65, h60⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h65 h45.symm h34.symm h23.symm h12.symm h01.symm h60.symm)
  have hseven : NoConsecutiveCyclePair (cycleNeighbors K 7) := by
    simp only [NoConsecutiveCyclePair, cycleNeighbors,
      Finset.mem_filter]
    simp only [show (0 : Fin 8) ∈ sixSet by decide,
      show (1 : Fin 8) ∈ sixSet by decide,
      show (2 : Fin 8) ∈ sixSet by decide,
      show (3 : Fin 8) ∈ sixSet by decide,
      show (4 : Fin 8) ∈ sixSet by decide,
      show (5 : Fin 8) ∈ sixSet by decide, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨h70, h71⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h70 h50.symm h45.symm h34.symm h23.symm h12.symm h71.symm)
    · rintro ⟨h71, h72⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h71 h01.symm h50.symm h45.symm h34.symm h23.symm h72.symm)
    · rintro ⟨h72, h73⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h72 h12.symm h01.symm h50.symm h45.symm h34.symm h73.symm)
    · rintro ⟨h73, h74⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h73 h23.symm h12.symm h01.symm h50.symm h45.symm h74.symm)
    · rintro ⟨h74, h75⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h74 h34.symm h23.symm h12.symm h01.symm h50.symm h75.symm)
    · rintro ⟨h75, h70⟩
      exact hno7 (graphHasCycleEmbedding7_of K (by decide)
        h75 h45.symm h34.symm h23.symm h12.symm h01.symm h70.symm)
  exact ⟨hsix, hseven⟩

/-- The paper's explicit Hamilton cycle when the two exterior vertices have
the two different alternating triples as their cycle neighborhoods. -/
theorem opposite_alternating_neighbors_give_eight_cycle
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hopp :
      (cycleNeighbors K 6 = evenCycleTriple ∧
        cycleNeighbors K 7 = oddCycleTriple) ∨
      (cycleNeighbors K 6 = oddCycleTriple ∧
        cycleNeighbors K 7 = evenCycleTriple)) :
    GraphHasCycleEmbedding K 8 := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  rcases hopp with ⟨h6e, h7o⟩ | ⟨h6o, h7e⟩
  · have h60 : K.Adj 6 0 := by
      apply adj_of_mem_cycleNeighbors
      rw [h6e]
      simp [evenCycleTriple]
    have h64 : K.Adj 6 4 := by
      apply adj_of_mem_cycleNeighbors
      rw [h6e]
      simp [evenCycleTriple]
    have h73 : K.Adj 7 3 := by
      apply adj_of_mem_cycleNeighbors
      rw [h7o]
      simp [oddCycleTriple]
    have h75 : K.Adj 7 5 := by
      apply adj_of_mem_cycleNeighbors
      rw [h7o]
      simp [oddCycleTriple]
    exact graphHasCycleEmbedding8_of K (by decide)
      h60 h01 h12 h23 h73.symm h75 h45.symm h64.symm
  · have h61 : K.Adj 6 1 := by
      apply adj_of_mem_cycleNeighbors
      rw [h6o]
      simp [oddCycleTriple]
    have h65 : K.Adj 6 5 := by
      apply adj_of_mem_cycleNeighbors
      rw [h6o]
      simp [oddCycleTriple]
    have h70 : K.Adj 7 0 := by
      apply adj_of_mem_cycleNeighbors
      rw [h7e]
      simp [evenCycleTriple]
    have h74 : K.Adj 7 4 := by
      apply adj_of_mem_cycleNeighbors
      rw [h7e]
      simp [evenCycleTriple]
    exact graphHasCycleEmbedding8_of K (by decide)
      h61 h12 h23 h34 h74.symm h70 h50.symm h65.symm

/-- In the common-even-triple case, every chord whose two ends lie in the
complementary odd triple is forbidden: the displayed chord and the exterior
vertex would give the paper's seven-cycle. -/
theorem odd_triple_chords_forbidden
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hno7 : ¬ GraphHasCycleEmbedding K 7)
    (h6e : cycleNeighbors K 6 = evenCycleTriple) :
    ¬ K.Adj 1 3 ∧ ¬ K.Adj 3 5 ∧ ¬ K.Adj 5 1 := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  have h60 : K.Adj 6 0 := by
    apply adj_of_mem_cycleNeighbors
    rw [h6e]
    simp [evenCycleTriple]
  have h62 : K.Adj 6 2 := by
    apply adj_of_mem_cycleNeighbors
    rw [h6e]
    simp [evenCycleTriple]
  have h64 : K.Adj 6 4 := by
    apply adj_of_mem_cycleNeighbors
    rw [h6e]
    simp [evenCycleTriple]
  refine ⟨?_, ?_, ?_⟩
  · intro h13
    exact hno7 (graphHasCycleEmbedding7_of K (by decide)
      h60 h50.symm h45.symm h34.symm h13.symm h12 h62.symm)
  · intro h35
    exact hno7 (graphHasCycleEmbedding7_of K (by decide)
      h62 h12.symm h01.symm h50.symm h35.symm h34 h64.symm)
  · intro h51
    exact hno7 (graphHasCycleEmbedding7_of K (by decide)
      h64 h34.symm h23.symm h12.symm h51.symm h50 h60.symm)

/-- The cyclic shift of `odd_triple_chords_forbidden`, for a common odd
alternating neighborhood. -/
theorem even_triple_chords_forbidden
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hno7 : ¬ GraphHasCycleEmbedding K 7)
    (h6o : cycleNeighbors K 6 = oddCycleTriple) :
    ¬ K.Adj 0 2 ∧ ¬ K.Adj 2 4 ∧ ¬ K.Adj 4 0 := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  have h61 : K.Adj 6 1 := by
    apply adj_of_mem_cycleNeighbors
    rw [h6o]
    simp [oddCycleTriple]
  have h63 : K.Adj 6 3 := by
    apply adj_of_mem_cycleNeighbors
    rw [h6o]
    simp [oddCycleTriple]
  have h65 : K.Adj 6 5 := by
    apply adj_of_mem_cycleNeighbors
    rw [h6o]
    simp [oddCycleTriple]
  refine ⟨?_, ?_, ?_⟩
  · intro h02
    exact hno7 (graphHasCycleEmbedding7_of K (by decide)
      h65 h45.symm h34.symm h23.symm h02.symm h01 h61.symm)
  · intro h24
    exact hno7 (graphHasCycleEmbedding7_of K (by decide)
      h61 h01.symm h50.symm h45.symm h24.symm h23 h63.symm)
  · intro h40
    exact hno7 (graphHasCycleEmbedding7_of K (by decide)
      h63 h23.symm h12.symm h01.symm h40.symm h45 h65.symm)

/-- The handshake count on the six induced vertices.  Since the induced
subgraph has eleven edges, the six cycle-degrees sum to twenty-two. -/
theorem six_cycle_degree_sum_eq_twenty_two
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hinside :
      (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card = 11) :
    (cycleNeighbors K 0).card + (cycleNeighbors K 1).card +
      (cycleNeighbors K 2).card + (cycleNeighbors K 3).card +
      (cycleNeighbors K 4).card + (cycleNeighbors K 5).card = 22 := by
  have hhand :
      (∑ x ∈ sixSet, (cycleNeighbors K x).card) =
        2 * (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card := by
    have hsum :=
      (K.induce (↑sixSet : Set (Fin 8))).sum_degrees_eq_twice_card_edges
    rw [← hsum, Finset.sum_subtype sixSet (by intro x; rfl)]
    apply Finset.sum_congr rfl
    intro x hx
    exact (induce_six_degree_eq_filter_card K x x.property).symm
  rw [hinside] at hhand
  have hsix : sixSet = ({0, 1, 2, 3, 4, 5} : Finset (Fin 8)) := by
    decide
  rw [hsix] at hhand
  simp [Finset.sum_insert] at hhand
  omega

/-- Indicator of a possible chord.  It is used only to expose the
paper's two chord classes as ordinary natural-number counts. -/
def edgeIndicator (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (x y : Fin 8) : ℕ :=
  if K.Adj x y then 1 else 0

theorem cycleNeighbors_card_eq_indicator_sum
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj] (x : Fin 8) :
    (cycleNeighbors K x).card =
      edgeIndicator K x 0 + edgeIndicator K x 1 +
      edgeIndicator K x 2 + edgeIndicator K x 3 +
      edgeIndicator K x 4 + edgeIndicator K x 5 := by
  have h := six_filter_card_eq_bool_sum
    (fun y ↦ decide (K.Adj x y))
  simp only [decide_eq_true_eq] at h
  by_cases h0 : K.Adj x 0 <;> by_cases h1 : K.Adj x 1 <;>
    by_cases h2 : K.Adj x 2 <;> by_cases h3 : K.Adj x 3 <;>
    by_cases h4 : K.Adj x 4 <;> by_cases h5 : K.Adj x 5 <;>
    simp [cycleNeighbors, edgeIndicator, h0, h1, h2, h3, h4, h5] at h ⊢
  all_goals exact h

/-- The paper's final chord classification and incidence contradiction in
the common-even case.  Here `r` counts type-I chords inside the common
alternating triple and `s` counts the three possible type-II chords. -/
theorem even_common_triple_incidence_contradiction
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hinside :
      (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card = 11)
    (hcycleDegree : ∀ x ∈ sixSet, (cycleNeighbors K x).card ≤ 4)
    (h13 : ¬ K.Adj 1 3) (h35 : ¬ K.Adj 3 5)
    (h51 : ¬ K.Adj 5 1) : False := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  have h05 : K.Adj 0 5 := h50.symm
  have h31 : ¬ K.Adj 3 1 := fun h ↦ h13 h.symm
  have h53 : ¬ K.Adj 5 3 := fun h ↦ h35 h.symm
  have h15 : ¬ K.Adj 1 5 := fun h ↦ h51 h.symm
  have hq0 := cycleNeighbors_card_eq_indicator_sum K 0
  have hq1 := cycleNeighbors_card_eq_indicator_sum K 1
  have hq2 := cycleNeighbors_card_eq_indicator_sum K 2
  have hq3 := cycleNeighbors_card_eq_indicator_sum K 3
  have hq4 := cycleNeighbors_card_eq_indicator_sum K 4
  have hq5 := cycleNeighbors_card_eq_indicator_sum K 5
  simp [edgeIndicator, K.loopless, h01, h12, h23, h34, h45, h50, h05,
    h13, h31, h35, h53, h51, h15, K.adj_comm] at hq0 hq1 hq2 hq3 hq4 hq5
  have hsum := six_cycle_degree_sum_eq_twenty_two K hinside
  have h0 := hcycleDegree 0 (by decide)
  have h2 := hcycleDegree 2 (by decide)
  have h4 := hcycleDegree 4 (by decide)
  let r := (if K.Adj 0 2 then 1 else 0) +
    (if K.Adj 2 4 then 1 else 0) + (if K.Adj 0 4 then 1 else 0)
  let s := (if K.Adj 0 3 then 1 else 0) +
    (if K.Adj 2 5 then 1 else 0) + (if K.Adj 1 4 then 1 else 0)
  have hi02 : (if K.Adj 0 2 then 1 else 0) ≤ 1 := by split <;> omega
  have hi24 : (if K.Adj 2 4 then 1 else 0) ≤ 1 := by split <;> omega
  have hi04 : (if K.Adj 0 4 then 1 else 0) ≤ 1 := by split <;> omega
  have hi03 : (if K.Adj 0 3 then 1 else 0) ≤ 1 := by split <;> omega
  have hi25 : (if K.Adj 2 5 then 1 else 0) ≤ 1 := by split <;> omega
  have hi14 : (if K.Adj 1 4 then 1 else 0) ≤ 1 := by split <;> omega
  have hrs : r + s = 5 := by
    dsimp [r, s]
    omega
  have hs3 : s ≤ 3 := by
    dsimp [s]
    omega
  have hr2 : 2 ≤ r := by omega
  have hincidence :
      (cycleNeighbors K 0).card + (cycleNeighbors K 2).card +
        (cycleNeighbors K 4).card = 6 + 2 * r + s := by
    dsimp [r, s]
    omega
  have hincidenceUpper :
      (cycleNeighbors K 0).card + (cycleNeighbors K 2).card +
        (cycleNeighbors K 4).card ≤ 12 := by omega
  omega

/-- The same paper count after cyclically shifting the two alternating
triples by one. -/
theorem odd_common_triple_incidence_contradiction
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hinside :
      (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card = 11)
    (hcycleDegree : ∀ x ∈ sixSet, (cycleNeighbors K x).card ≤ 4)
    (h02 : ¬ K.Adj 0 2) (h24 : ¬ K.Adj 2 4)
    (h40 : ¬ K.Adj 4 0) : False := by
  rcases hcanonical with ⟨h01, h12, h23, h34, h45, h50⟩
  have h05 : K.Adj 0 5 := h50.symm
  have h20 : ¬ K.Adj 2 0 := fun h ↦ h02 h.symm
  have h42 : ¬ K.Adj 4 2 := fun h ↦ h24 h.symm
  have h04 : ¬ K.Adj 0 4 := fun h ↦ h40 h.symm
  have hq0 := cycleNeighbors_card_eq_indicator_sum K 0
  have hq1 := cycleNeighbors_card_eq_indicator_sum K 1
  have hq2 := cycleNeighbors_card_eq_indicator_sum K 2
  have hq3 := cycleNeighbors_card_eq_indicator_sum K 3
  have hq4 := cycleNeighbors_card_eq_indicator_sum K 4
  have hq5 := cycleNeighbors_card_eq_indicator_sum K 5
  simp [edgeIndicator, K.loopless, h01, h12, h23, h34, h45, h50, h05,
    h02, h20, h24, h42, h40, h04, K.adj_comm] at hq0 hq1 hq2 hq3 hq4 hq5
  have hsum := six_cycle_degree_sum_eq_twenty_two K hinside
  have h1 := hcycleDegree 1 (by decide)
  have h3 := hcycleDegree 3 (by decide)
  have h5 := hcycleDegree 5 (by decide)
  let r := (if K.Adj 1 3 then 1 else 0) +
    (if K.Adj 3 5 then 1 else 0) + (if K.Adj 1 5 then 1 else 0)
  let s := (if K.Adj 0 3 then 1 else 0) +
    (if K.Adj 2 5 then 1 else 0) + (if K.Adj 1 4 then 1 else 0)
  have hi13 : (if K.Adj 1 3 then 1 else 0) ≤ 1 := by split <;> omega
  have hi35 : (if K.Adj 3 5 then 1 else 0) ≤ 1 := by split <;> omega
  have hi15 : (if K.Adj 1 5 then 1 else 0) ≤ 1 := by split <;> omega
  have hi03 : (if K.Adj 0 3 then 1 else 0) ≤ 1 := by split <;> omega
  have hi25 : (if K.Adj 2 5 then 1 else 0) ≤ 1 := by split <;> omega
  have hi14 : (if K.Adj 1 4 then 1 else 0) ≤ 1 := by split <;> omega
  have hrs : r + s = 5 := by
    dsimp [r, s]
    omega
  have hs3 : s ≤ 3 := by
    dsimp [s]
    omega
  have hr2 : 2 ≤ r := by omega
  have hincidence :
      (cycleNeighbors K 1).card + (cycleNeighbors K 3).card +
        (cycleNeighbors K 5).card = 6 + 2 * r + s := by
    dsimp [r, s]
    omega
  have hincidenceUpper :
      (cycleNeighbors K 1).card + (cycleNeighbors K 3).card +
        (cycleNeighbors K 5).card ≤ 12 := by omega
  omega

/-- The complete exceptional-case proof, following the manuscript's
classification rather than a truth-table certificate.  Each branch either
constructs the displayed forbidden long cycle or reaches the final
chord-incidence contradiction. -/
theorem exceptional_fin8_impossible_paper
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    (hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (hedges : K.edgeFinset.card = 17)
    (hinside :
      (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card = 11)
    (hmindegree : ∀ x, 3 ≤ K.degree x)
    (hcycleDegree : ∀ x ∈ sixSet, (cycleNeighbors K x).card ≤ 4)
    (hno7 : ¬ GraphHasCycleEmbedding K 7)
    (hno8 : ¬ GraphHasCycleEmbedding K 8) : False := by
  have hdecomp := edge_count_finset_decomposition K sixSet
  rw [hedges, hinside, outside_sixSet_edge_card K,
    crossing_sixSet_card_eq_cycleNeighbors_add K] at hdecomp
  by_cases h67 : K.Adj 6 7
  · have hsum :
        (cycleNeighbors K 6).card + (cycleNeighbors K 7).card = 5 := by
      simp [h67] at hdecomp
      omega
    have hd6 := degree_six_eq_cycleNeighbors_add K
    have hd7 := degree_seven_eq_cycleNeighbors_add K
    rw [if_pos h67] at hd6 hd7
    have h6lower : 2 ≤ (cycleNeighbors K 6).card := by
      have := hmindegree 6
      omega
    have h7lower : 2 ≤ (cycleNeighbors K 7).card := by
      have := hmindegree 7
      omega
    have hone : (cycleNeighbors K 6).card = 3 ∨
        (cycleNeighbors K 7).card = 3 := by
      omega
    have hshort : HasShortOrientedPair
        (cycleNeighbors K 6) (cycleNeighbors K 7) := by
      rcases hone with h6card | h7card
      · exact short_oriented_pair_of_card_three_two
          (cycleNeighbors K 6) (cycleNeighbors K 7)
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          h6card h7lower
      · exact (short_oriented_pair_of_card_three_two
          (cycleNeighbors K 7) (cycleNeighbors K 6)
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          h7card h6lower).swap
    rcases long_cycle_of_adjacent_outside_short_pair K hcanonical h67 hshort
      with h7 | h8
    · exact hno7 h7
    · exact hno8 h8
  · have hsum :
        (cycleNeighbors K 6).card + (cycleNeighbors K 7).card = 6 := by
      simp [h67] at hdecomp
      omega
    have hd6 := degree_six_eq_cycleNeighbors_add K
    have hd7 := degree_seven_eq_cycleNeighbors_add K
    rw [if_neg h67] at hd6 hd7
    have h6lower : 3 ≤ (cycleNeighbors K 6).card := by
      have := hmindegree 6
      omega
    have h7lower : 3 ≤ (cycleNeighbors K 7).card := by
      have := hmindegree 7
      omega
    have h6card : (cycleNeighbors K 6).card = 3 := by omega
    have h7card : (cycleNeighbors K 7).card = 3 := by omega
    obtain ⟨h6ind, h7ind⟩ :=
      no_consecutive_cycle_neighbors K hcanonical hno7
    have h6class := independent_cycle_triple_classification
      (cycleNeighbors K 6) (Finset.filter_subset _ _) h6card h6ind
    have h7class := independent_cycle_triple_classification
      (cycleNeighbors K 7) (Finset.filter_subset _ _) h7card h7ind
    rcases h6class with h6e | h6o <;>
      rcases h7class with h7e | h7o
    · obtain ⟨h13, h35, h51⟩ :=
        odd_triple_chords_forbidden K hcanonical hno7 h6e
      exact even_common_triple_incidence_contradiction K hcanonical hinside
        hcycleDegree h13 h35 h51
    · exact hno8 (opposite_alternating_neighbors_give_eight_cycle K
        hcanonical (Or.inl ⟨h6e, h7o⟩))
    · exact hno8 (opposite_alternating_neighbors_give_eight_cycle K
        hcanonical (Or.inr ⟨h6o, h7e⟩))
    · obtain ⟨h02, h24, h40⟩ :=
        even_triple_chords_forbidden K hcanonical hno7 h6o
      exact odd_common_triple_incidence_contradiction K hcanonical hinside
        hcycleDegree h02 h24 h40

end

end Erdos767
