import Erdos767.Basic
import Erdos767.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Set.Card

/-!
# Lower-bound constructions

This file begins the formalization of the two lower-bound constructions in
Section 3 of `ErdosProblem767.tex`.

The reusable graph-theoretic degree argument is complete.  The concrete cyclic
and split graphs are defined as in the paper.  This file proves the cyclic
maximum-degree bound, the resulting path-fan freeness of the nearly regular
construction, its exact edge count, and the basic adjacency/degree laws of the
split graph, including its exact edge count.  The split graph's
path-alternation bound remains next.
-/

open scoped Sym2

namespace Erdos767

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A graph is `PF_ell`-free when it has no path-fan with `ell` neighbors at
its center. -/
def PathFanFree (G : SimpleGraph V) [DecidableRel G.Adj] (ell : ℕ) : Prop :=
  ¬ HasPathFan G ell

/-- The neighbors of a path-fan center that occur on its path form a subset of
the full neighbor finset of the center. -/
theorem walkNeighbors_subset_neighborFinset {x u v : V} (p : G.Walk u v) :
    walkNeighbors x p ⊆ G.neighborFinset x := by
  intro w hw
  exact G.mem_neighborFinset x w |>.mpr (Finset.mem_filter.mp hw).2

theorem card_walkNeighbors_le_degree {x u v : V} (p : G.Walk u v) :
    (walkNeighbors x p).card ≤ G.degree x := by
  exact Finset.card_le_card (walkNeighbors_subset_neighborFinset p)

omit [DecidableEq V] in
  /-- An instance-independent form of the finite degree: the cardinality of
  the neighbor set equals Mathlib's finset-based degree. -/
  theorem ncard_neighborSet_eq_degree (x : V) :
      (G.neighborSet x).ncard = G.degree x := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]

omit [DecidableEq V] in
  /-- The instance-independent cardinality of the edge set equals the cardinality
  of Mathlib's finite edge representation. -/
  theorem ncard_edgeSet_eq_card_edgeFinset :
      G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl

/-- Every path-fan center has degree at least the order of the fan. -/
theorem HasPathFan.exists_degree_ge {ell : ℕ} (h : HasPathFan G ell) :
    ∃ x : V, ell ≤ G.degree x := by
  rcases h with ⟨x, u, v, p, -, -, hcount⟩
  exact ⟨x, hcount.trans (card_walkNeighbors_le_degree p)⟩

/-- A uniform strict degree bound excludes path-fans. -/
theorem pathFanFree_of_forall_degree_lt {ell : ℕ}
    (hdeg : ∀ x : V, G.degree x < ell) : PathFanFree G ell := by
  intro hfan
  obtain ⟨x, hx⟩ := hfan.exists_degree_ge
  exact (not_le_of_gt (hdeg x)) hx

/-- The degree observation used for the nearly-regular lower-bound graph. -/
theorem pathFanFree_succ_of_forall_degree_le {d : ℕ}
    (hdeg : ∀ x : V, G.degree x ≤ d) : PathFanFree G (d + 1) := by
  apply pathFanFree_of_forall_degree_lt
  intro x
  exact Nat.lt_succ_of_le (hdeg x)

section CyclicCore

/-- Positive jumps `1, ..., floor(d/2)` in the cyclic group `Fin n`. -/
def cyclicJumps (d n : ℕ) : Set (Fin n) :=
  {j | 1 ≤ j.val ∧ j.val ≤ d / 2}

instance cyclicJumps_decidablePred (d n : ℕ) : DecidablePred (· ∈ cyclicJumps d n) :=
  fun j => inferInstanceAs (Decidable (1 ≤ j.val ∧ j.val ≤ d / 2))

def cyclicJumpFinset (d n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (· ∈ cyclicJumps d n)

theorem card_cyclicJumpFinset_le (d n : ℕ) :
    (cyclicJumpFinset d n).card ≤ d / 2 := by
  have hsub : (cyclicJumpFinset d n).map Fin.valEmbedding ⊆ Finset.Icc 1 (d / 2) := by
    intro j hj
    rw [Finset.mem_Icc]
    rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
    have hiBounds : 1 ≤ i.val ∧ i.val ≤ d / 2 := by
      have hi' := (Finset.mem_filter.mp hi).2
      exact hi'
    exact hij ▸ hiBounds
  calc
    (cyclicJumpFinset d n).card = ((cyclicJumpFinset d n).map Fin.valEmbedding).card := by
      symm
      exact Finset.card_map _
    _ ≤ (Finset.Icc 1 (d / 2)).card := Finset.card_le_card hsub
    _ = d / 2 := by simp

/-- When the target degree is below the group order, all jumps
`1, ..., floor(d/2)` occur as distinct elements of `Fin n`. -/
theorem card_cyclicJumpFinset_eq (d n : ℕ) (hdn : d < n) :
    (cyclicJumpFinset d n).card = d / 2 := by
  let f : Fin (d / 2) ↪ Fin n :=
    { toFun := fun j => ⟨j.val + 1, by omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact Nat.add_right_cancel (congrArg Fin.val hij) }
  have hsub : Finset.univ.map f ⊆ cyclicJumpFinset d n := by
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨i, -, rfl⟩
    simp only [cyclicJumpFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    change 1 ≤ (f i).val ∧ (f i).val ≤ d / 2
    change 1 ≤ i.val + 1 ∧ i.val + 1 ≤ d / 2
    omega
  apply Nat.le_antisymm (card_cyclicJumpFinset_le d n)
  calc
    d / 2 = (Finset.univ : Finset (Fin (d / 2))).card := by simp
    _ = (Finset.univ.map f).card := (Finset.card_map _).symm
    _ ≤ (cyclicJumpFinset d n).card := Finset.card_le_card hsub

def cyclicNeighborCandidates (d n : ℕ) [NeZero n] (i : Fin n) : Finset (Fin n) :=
  (cyclicJumpFinset d n).image (fun j => i - j) ∪
    (cyclicJumpFinset d n).image (fun j => i + j)

theorem circulant_neighborFinset_subset_candidates (d n : ℕ) [NeZero n] (i : Fin n) :
    (SimpleGraph.circulantGraph (cyclicJumps d n)).neighborFinset i ⊆
      cyclicNeighborCandidates d n i := by
  intro w hw
  have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
  rw [SimpleGraph.circulantGraph_adj] at hadj
  rcases hadj.2 with h | h
  · apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨i - w, ?_, ?_⟩
    · simpa [cyclicJumpFinset] using h
    · apply Fin.ext
      simp
  · apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨w - i, ?_, ?_⟩
    · simpa [cyclicJumpFinset] using h
    · apply Fin.ext
      simp

theorem cyclicNeighborCandidates_subset_neighborFinset
    (d n : ℕ) [NeZero n] (i : Fin n) :
    cyclicNeighborCandidates d n i ⊆
      (SimpleGraph.circulantGraph (cyclicJumps d n)).neighborFinset i := by
  intro w hw
  rw [cyclicNeighborCandidates, Finset.mem_union] at hw
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.circulantGraph_adj]
  rcases hw with hw | hw
  · rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    have hjBounds : 1 ≤ j.val ∧ j.val ≤ d / 2 := (Finset.mem_filter.mp hj).2
    constructor
    · intro hEq
      have : j = 0 := by
        apply sub_right_injective (b := i)
        simpa using hEq.symm
      have hval := congrArg Fin.val this
      change j.val = 0 at hval
      omega
    · left
      simpa [cyclicJumps] using hjBounds
  · rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    have hjBounds : 1 ≤ j.val ∧ j.val ≤ d / 2 := (Finset.mem_filter.mp hj).2
    constructor
    · intro hEq
      have : j = 0 := by
        apply add_right_injective i
        simpa using hEq.symm
      have hval := congrArg Fin.val this
      change j.val = 0 at hval
      omega
    · right
      simpa [cyclicJumps] using hjBounds

theorem circulant_neighborFinset_eq_candidates
    (d n : ℕ) [NeZero n] (i : Fin n) :
    (SimpleGraph.circulantGraph (cyclicJumps d n)).neighborFinset i =
      cyclicNeighborCandidates d n i := by
  exact Finset.Subset.antisymm
    (circulant_neighborFinset_subset_candidates d n i)
    (cyclicNeighborCandidates_subset_neighborFinset d n i)

/-- The negative and positive jump neighbors do not overlap when `d < n`. -/
theorem cyclicNeighborCandidates_disjoint
    (d n : ℕ) [NeZero n] (hdn : d < n) (i : Fin n) :
    Disjoint
      ((cyclicJumpFinset d n).image (fun j => i - j))
      ((cyclicJumpFinset d n).image (fun j => i + j)) := by
  rw [Finset.disjoint_left]
  intro w hwMinus hwPlus
  rcases Finset.mem_image.mp hwMinus with ⟨j, hj, hjw⟩
  rcases Finset.mem_image.mp hwPlus with ⟨j', hj', hjw'⟩
  have hjBounds : 1 ≤ j.val ∧ j.val ≤ d / 2 := (Finset.mem_filter.mp hj).2
  have hj'Bounds : 1 ≤ j'.val ∧ j'.val ≤ d / 2 := (Finset.mem_filter.mp hj').2
  have heq : i - j = i + j' := hjw.trans hjw'.symm
  have hneg : -j = j' := by
    apply add_left_cancel (a := i)
    simpa [sub_eq_add_neg] using heq
  have hsum : j + j' = 0 := by simp [← hneg]
  have hval := congrArg Fin.val hsum
  simp only [Fin.val_add] at hval
  change (j.val + j'.val) % n = 0 at hval
  have hsum_lt : j.val + j'.val < n := by omega
  rw [Nat.mod_eq_of_lt hsum_lt] at hval
  omega

/-- Exact regular degree of the cyclic core in the manuscript's range. -/
theorem circulant_degree_eq (d n : ℕ) [NeZero n] (hdn : d < n) (i : Fin n) :
    (SimpleGraph.circulantGraph (cyclicJumps d n)).degree i = 2 * (d / 2) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    circulant_neighborFinset_eq_candidates, cyclicNeighborCandidates]
  rw [Finset.card_union_eq_card_add_card.mpr
    (cyclicNeighborCandidates_disjoint d n hdn i)]
  rw [Finset.card_image_of_injective _ sub_right_injective,
    Finset.card_image_of_injective _ (add_right_injective i),
    card_cyclicJumpFinset_eq d n hdn]
  omega

/-- Exact edge count of the cyclic core, obtained from its regular degree and
the degree-sum formula. -/
theorem circulant_card_edgeFinset_eq
    (d n : ℕ) [NeZero n] (hdn : d < n) :
    (SimpleGraph.circulantGraph (cyclicJumps d n)).edgeFinset.card =
      (d / 2) * n := by
  let C := SimpleGraph.circulantGraph (cyclicJumps d n)
  have hsum := C.sum_degrees_eq_twice_card_edges
  have htwo :
      2 * C.edgeFinset.card = 2 * ((d / 2) * n) := by
    calc
      2 * C.edgeFinset.card = ∑ i : Fin n, C.degree i := hsum.symm
      _ = ∑ _i : Fin n, 2 * (d / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        exact circulant_degree_eq d n hdn i
      _ = 2 * ((d / 2) * n) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.mul_left_cancel (by omega) htwo

theorem circulant_degree_le (d n : ℕ) [NeZero n] (i : Fin n) :
    (SimpleGraph.circulantGraph (cyclicJumps d n)).degree i ≤ 2 * (d / 2) := by
  calc
    (SimpleGraph.circulantGraph (cyclicJumps d n)).degree i =
        ((SimpleGraph.circulantGraph (cyclicJumps d n)).neighborFinset i).card := rfl
    _ ≤ (cyclicNeighborCandidates d n i).card :=
      Finset.card_le_card (circulant_neighborFinset_subset_candidates d n i)
    _ ≤ (cyclicJumpFinset d n).card + (cyclicJumpFinset d n).card := by
      unfold cyclicNeighborCandidates
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    _ ≤ d / 2 + d / 2 := Nat.add_le_add (card_cyclicJumpFinset_le d n)
      (card_cyclicJumpFinset_le d n)
    _ = 2 * (d / 2) := by omega

/-- The extra matching used when the target degree `d` is odd.  It joins
`i` to `i + floor(n/2)` for `0 ≤ i < floor(n/2)`. -/
def halfShiftMatching (n : ℕ) [NeZero n] : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun (i j : Fin n) =>
    i.val < n / 2 ∧ j = i + Fin.ofNat n (n / 2)

instance halfShiftMatching_decidableAdj (n : ℕ) [NeZero n] :
    DecidableRel (halfShiftMatching n).Adj := by
  unfold halfShiftMatching
  infer_instance

/-- The half-shift edges form a matching: every vertex has at most one
neighbor in this graph. -/
theorem halfShiftMatching_degree_le_one (n : ℕ) [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (halfShiftMatching n).degree i ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro w z hw hz
  have haw := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
  have haz := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
  simp only [halfShiftMatching, SimpleGraph.fromRel_adj] at haw haz
  rcases haw.2 with hwForward | hwBackward
  · rcases haz.2 with hzForward | hzBackward
    · exact hwForward.2.trans hzForward.2.symm
    · exfalso
      have hm_lt : n / 2 < n := by omega
      have hz_add_lt : z.val + n / 2 < n := by omega
      have hval := congrArg Fin.val hzBackward.2
      simp only [Fin.val_add] at hval
      have hshift : (Fin.ofNat n (n / 2)).val = n / 2 := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt hm_lt]
      rw [hshift, Nat.mod_eq_of_lt hz_add_lt] at hval
      omega
  · rcases haz.2 with hzForward | hzBackward
    · exfalso
      have hm_lt : n / 2 < n := by omega
      have hw_add_lt : w.val + n / 2 < n := by omega
      have hval := congrArg Fin.val hwBackward.2
      simp only [Fin.val_add] at hval
      have hshift : (Fin.ofNat n (n / 2)).val = n / 2 := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt hm_lt]
      rw [hshift, Nat.mod_eq_of_lt hw_add_lt] at hval
      omega
    · exact add_right_cancel (hwBackward.2.symm.trans hzBackward.2)

/-- The copy of a lower-half index inside `Fin n`. -/
def lowerHalfVertex (n : ℕ) [NeZero n] (i : Fin (n / 2)) : Fin n :=
  ⟨i.val, by omega⟩

/-- The matching edge indexed by a lower-half vertex. -/
def halfShiftEdge (n : ℕ) [NeZero n] (i : Fin (n / 2)) : Sym2 (Fin n) :=
  s(lowerHalfVertex n i,
    lowerHalfVertex n i + Fin.ofNat n (n / 2))

/-- Distinct lower-half indices give distinct unordered matching edges. -/
def halfShiftEdgeEmbedding (n : ℕ) [NeZero n] : Fin (n / 2) ↪ Sym2 (Fin n) where
  toFun := halfShiftEdge n
  inj' := by
    intro i j hij
    change
      s(lowerHalfVertex n i, lowerHalfVertex n i + Fin.ofNat n (n / 2)) =
      s(lowerHalfVertex n j, lowerHalfVertex n j + Fin.ofNat n (n / 2)) at hij
    rw [Sym2.eq_iff] at hij
    rcases hij with hij | hij
    · apply Fin.ext
      have hval := congrArg Fin.val hij.1
      change i.val = j.val at hval
      exact hval
    · exfalso
      have hi := i.isLt
      have hj := j.isLt
      have hm_lt : n / 2 < n := by omega
      have hj_add_lt : j.val + n / 2 < n := by omega
      have hval := congrArg Fin.val hij.1
      change i.val = (j.val + (n / 2 % n)) % n at hval
      rw [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hj_add_lt] at hval
      omega

theorem halfShiftEdge_mem_edgeFinset
    (n : ℕ) [NeZero n] (i : Fin (n / 2)) :
    halfShiftEdge n i ∈ (halfShiftMatching n).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  unfold halfShiftEdge
  rw [SimpleGraph.mem_edgeSet]
  simp only [halfShiftMatching, SimpleGraph.fromRel_adj]
  constructor
  · intro hEq
    have hi := i.isLt
    have hm_lt : n / 2 < n := by omega
    have hi_add_lt : i.val + n / 2 < n := by omega
    have hval := congrArg Fin.val hEq
    change i.val = (i.val + (n / 2 % n)) % n at hval
    rw [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hi_add_lt] at hval
    omega
  · left
    exact ⟨i.isLt, True.intro⟩

/-- The edge finset of the half-shift matching is exactly the image of its
lower-half indices. -/
theorem halfShiftMatching_edgeFinset_eq (n : ℕ) [NeZero n] :
    (halfShiftMatching n).edgeFinset =
      Finset.univ.map (halfShiftEdgeEmbedding n) := by
  classical
  ext e
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        simp only [halfShiftMatching, SimpleGraph.fromRel_adj] at he
        rcases he.2 with hxy | hyx
        · let i : Fin (n / 2) := ⟨x.val, hxy.1⟩
          apply Finset.mem_map.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          change halfShiftEdge n i = s(x, y)
          have hix : lowerHalfVertex n i = x := by
            apply Fin.ext
            rfl
          rw [halfShiftEdge, hix, hxy.2]
        · let i : Fin (n / 2) := ⟨y.val, hyx.1⟩
          apply Finset.mem_map.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          change halfShiftEdge n i = s(x, y)
          have hiy : lowerHalfVertex n i = y := by
            apply Fin.ext
            rfl
          rw [halfShiftEdge, hiy, hyx.2]
          exact Sym2.eq_swap
  · intro he
    rcases Finset.mem_map.mp he with ⟨i, -, hie⟩
    rw [← hie]
    exact halfShiftEdge_mem_edgeFinset n i

/-- The half-shift matching has exactly `floor(n/2)` edges. -/
theorem halfShiftMatching_card_edgeFinset (n : ℕ) [NeZero n] :
    (halfShiftMatching n).edgeFinset.card = n / 2 := by
  rw [halfShiftMatching_edgeFinset_eq, Finset.card_map,
    Finset.card_univ, Fintype.card_fin]

/-- For odd `d < n`, the long half-shift edges are not among the short cyclic
jump edges. -/
theorem circulant_disjoint_halfShiftMatching
    (d n : ℕ) [NeZero n] (hdOdd : Odd d) (hdn : d < n) :
    Disjoint (SimpleGraph.circulantGraph (cyclicJumps d n))
      (halfShiftMatching n) := by
  have hdform := Nat.two_mul_div_two_add_one_of_odd hdOdd
  have hfloor : d / 2 < n / 2 := by omega
  have hm_lt : n / 2 < n := by omega
  rw [SimpleGraph.disjoint_left]
  intro x y hcir hmatch
  rw [SimpleGraph.circulantGraph_adj] at hcir
  simp only [halfShiftMatching, SimpleGraph.fromRel_adj] at hmatch
  have hrel : ∀ u v : Fin n,
      (u.val < n / 2 ∧ v = u + Fin.ofNat n (n / 2)) →
      ¬(SimpleGraph.circulantGraph (cyclicJumps d n)).Adj u v := by
    intro u v huv hadj
    rw [SimpleGraph.circulantGraph_adj] at hadj
    rcases hadj.2 with hneg | hpos
    · change 1 ≤ (u - v).val ∧ (u - v).val ≤ d / 2 at hneg
      have hzero : (u - v) + Fin.ofNat n (n / 2) = 0 := by
        rw [huv.2]
        simp
      have hval := congrArg Fin.val hzero
      simp only [Fin.val_add] at hval
      change ((u - v).val + (n / 2 % n)) % n = 0 at hval
      rw [Nat.mod_eq_of_lt hm_lt] at hval
      have hadd_lt : (u - v).val + n / 2 < n := by omega
      rw [Nat.mod_eq_of_lt hadd_lt] at hval
      omega
    · change 1 ≤ (v - u).val ∧ (v - u).val ≤ d / 2 at hpos
      have heq : v - u = Fin.ofNat n (n / 2) := by
        rw [huv.2]
        simp
      have hval := congrArg Fin.val heq
      change (v - u).val = n / 2 % n at hval
      rw [Nat.mod_eq_of_lt hm_lt] at hval
      omega
  rcases hmatch.2 with hxy | hyx
  · exact hrel x y hxy hcir
  · apply hrel y x hyx
    rw [SimpleGraph.circulantGraph_adj]
    exact ⟨Ne.symm hcir.1, hcir.2.elim Or.inr Or.inl⟩

private theorem even_half_product_identity
    (d n : ℕ) (hdEven : Even d) :
    (d / 2) * n = (d * n) / 2 := by
  have hdform := Nat.two_mul_div_two_of_even hdEven
  calc
    (d / 2) * n = (2 * ((d / 2) * n)) / 2 := by omega
    _ = ((2 * (d / 2)) * n) / 2 := by simp [Nat.mul_assoc]
    _ = (d * n) / 2 :=
      congrArg (fun x : ℕ => x / 2) (congrArg (fun x : ℕ => x * n) hdform)

private theorem odd_half_product_identity
    (d n : ℕ) (hdOdd : Odd d) :
    (d / 2) * n + n / 2 = (d * n) / 2 := by
  have hdform := Nat.two_mul_div_two_add_one_of_odd hdOdd
  have hdiv :
      (2 * ((d / 2) * n) + n) / 2 = (d / 2) * n + n / 2 := by
    rw [Nat.add_comm, Nat.add_mul_div_left n ((d / 2) * n) (by omega), Nat.add_comm]
  calc
    (d / 2) * n + n / 2 = (2 * ((d / 2) * n) + n) / 2 := hdiv.symm
    _ = ((2 * (d / 2) + 1) * n) / 2 := by
      simp [Nat.add_mul, Nat.mul_assoc]
    _ = (d * n) / 2 :=
      congrArg (fun x : ℕ => x / 2) (congrArg (fun x : ℕ => x * n) hdform)

/-- A cyclic graph of target degree `d`: symmetric jumps up to `floor(d/2)`,
plus the half-shift matching when `d` is odd. -/
def cyclicDegreeGraph (d n : ℕ) [NeZero n] : SimpleGraph (Fin n) :=
  SimpleGraph.circulantGraph (cyclicJumps d n) ⊔
    if Odd d then halfShiftMatching n else ⊥

noncomputable instance cyclicDegreeGraph_decidableAdj (d n : ℕ) [NeZero n] :
    DecidableRel (cyclicDegreeGraph d n).Adj := by
  classical
  unfold cyclicDegreeGraph
  infer_instance

/-- Instance-independent exact edge count for the cyclic construction. -/
theorem cyclicDegreeGraph_ncard_edgeSet_eq
    (d n : ℕ) [NeZero n] (hdn : d < n) :
    (cyclicDegreeGraph d n).edgeSet.ncard = (d * n) / 2 := by
  classical
  by_cases hdOdd : Odd d
  · unfold cyclicDegreeGraph
    rw [if_pos hdOdd, SimpleGraph.edgeSet_sup]
    rw [Set.ncard_union_eq
      (SimpleGraph.disjoint_edgeSet.mpr
        (circulant_disjoint_halfShiftMatching d n hdOdd hdn))]
    rw [ncard_edgeSet_eq_card_edgeFinset,
      ncard_edgeSet_eq_card_edgeFinset,
      circulant_card_edgeFinset_eq d n hdn,
      halfShiftMatching_card_edgeFinset]
    exact odd_half_product_identity d n hdOdd
  · have hdEven : Even d := Nat.not_odd_iff_even.mp hdOdd
    unfold cyclicDegreeGraph
    rw [if_neg hdOdd, sup_bot_eq]
    rw [ncard_edgeSet_eq_card_edgeFinset,
      circulant_card_edgeFinset_eq d n hdn]
    exact even_half_product_identity d n hdEven

/-- Exact number of edges in the cyclic construction of target degree `d`. -/
theorem cyclicDegreeGraph_card_edgeFinset_eq
    (d n : ℕ) [NeZero n] (hdn : d < n) :
    (cyclicDegreeGraph d n).edgeFinset.card = (d * n) / 2 := by
  rw [← ncard_edgeSet_eq_card_edgeFinset]
  exact cyclicDegreeGraph_ncard_edgeSet_eq d n hdn

/-- Under the range relevant to the paper (`2 ≤ n`), the cyclic construction
has neighbor-set cardinality at most its target degree. -/
theorem cyclicDegreeGraph_ncard_neighborSet_le
    (d n : ℕ) [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    ((cyclicDegreeGraph d n).neighborSet i).ncard ≤ d := by
  classical
  by_cases hd : Odd d
  · unfold cyclicDegreeGraph
    rw [if_pos hd]
    rw [SimpleGraph.neighborSet_sup]
    calc
      _ ≤ ((SimpleGraph.circulantGraph (cyclicJumps d n)).neighborSet i).ncard +
          ((halfShiftMatching n).neighborSet i).ncard := Set.ncard_union_le _ _
      _ = (SimpleGraph.circulantGraph (cyclicJumps d n)).degree i +
          (halfShiftMatching n).degree i := by
            rw [ncard_neighborSet_eq_degree, ncard_neighborSet_eq_degree]
      _ ≤ 2 * (d / 2) + 1 :=
        Nat.add_le_add (circulant_degree_le d n i)
          (halfShiftMatching_degree_le_one n hn i)
      _ = d := Nat.two_mul_div_two_add_one_of_odd hd
  · have heven : Even d := Nat.not_odd_iff_even.mp hd
    unfold cyclicDegreeGraph
    rw [if_neg hd, sup_bot_eq]
    rw [ncard_neighborSet_eq_degree]
    simpa [Nat.two_mul_div_two_of_even heven] using circulant_degree_le d n i

/-- Degree formulation of `cyclicDegreeGraph_ncard_neighborSet_le`. -/
theorem cyclicDegreeGraph_degree_le (d n : ℕ) [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (cyclicDegreeGraph d n).degree i ≤ d := by
  rw [← ncard_neighborSet_eq_degree]
  exact cyclicDegreeGraph_ncard_neighborSet_le d n hn i

/-- The nearly-regular construction in the paper. -/
abbrev nearlyRegularGraph (k n : ℕ) [NeZero n] : SimpleGraph (Fin n) :=
  cyclicDegreeGraph (k + 1) n

/-- The nearly regular construction has exactly `t_k(n)` edges in the paper's
range `n ≥ k+2`. -/
theorem nearlyRegularGraph_card_edgeFinset_eq_t
    (k n : ℕ) [NeZero n] (hn : k + 2 ≤ n) :
    (nearlyRegularGraph k n).edgeFinset.card = t k n := by
  have hdn : k + 1 < n := by omega
  simpa [t] using cyclicDegreeGraph_card_edgeFinset_eq (k + 1) n hdn

/-- The nearly-regular lower-bound construction contains no `PF_(k+2)`.
This is the first complete construction-level consequence used in the paper. -/
theorem nearlyRegularGraph_pathFanFree (k n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    PathFanFree (nearlyRegularGraph k n) (k + 2) := by
  apply pathFanFree_succ_of_forall_degree_le
  intro i
  simpa [Nat.add_assoc] using cyclicDegreeGraph_degree_le (k + 1) n hn i

end CyclicCore

section Split

/-- The edge cardinality of a disjoint sum is the sum of the two edge
cardinalities. -/
theorem ncard_edgeSet_sum_eq {U W : Type*} [Finite U] [Finite W]
    (G : SimpleGraph U) (H : SimpleGraph W) :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
  change Nat.card (G ⊕g H).edgeSet =
    Nat.card G.edgeSet + Nat.card H.edgeSet
  rw [Nat.card_congr SimpleGraph.edgeSetSumEquiv, Nat.card_sum]

instance completeBipartiteGraph_decidableAdj (U W : Type*) :
    DecidableRel (completeBipartiteGraph U W).Adj := by
  unfold completeBipartiteGraph
  infer_instance

/-- A complete bipartite graph on `Fin a ⊕ Fin b` has exactly `a*b` edges. -/
theorem completeBipartiteGraph_card_edgeFinset (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeFinset.card = a * b := by
  classical
  rw [← ncard_edgeSet_eq_card_edgeFinset,
    SimpleGraph.edgeSet_completeBipartiteGraph,
    Set.ncard_range_of_injective (by grind [Function.Injective])]
  simp

/-- Edges internal to the two summands are disjoint from all complete
bipartite cross edges. -/
theorem sum_disjoint_completeBipartiteGraph
    {U W : Type*} (G : SimpleGraph U) (H : SimpleGraph W) :
    Disjoint (G ⊕g H) (completeBipartiteGraph U W) := by
  rw [SimpleGraph.disjoint_left]
  rintro (u | w) (u' | w') hadj <;> simp_all

/-- The split construction on `Fin a ⊕ Fin (n-a)`.  Its left side contains
the cyclic graph of target degree `k+1-a`, its right side is independent, and
all cross edges are present. -/
def splitGraph (k n a : ℕ) [NeZero a] : SimpleGraph (Fin a ⊕ Fin (n - a)) :=
  (cyclicDegreeGraph (k + 1 - a) a ⊕g (⊥ : SimpleGraph (Fin (n - a)))) ⊔
    completeBipartiteGraph (Fin a) (Fin (n - a))

noncomputable instance splitGraph_decidableAdj (k n a : ℕ) [NeZero a] :
    DecidableRel (splitGraph k n a).Adj := by
  classical
  unfold splitGraph
  infer_instance

/-- The split construction has the exact number of edges claimed in the
manuscript for every admissible `a ∈ A_k`. -/
theorem splitGraph_card_edgeFinset_eq_splitTerm
    (k n a : ℕ) [NeZero a] (ha : a ∈ A k) :
    (splitGraph k n a).edgeFinset.card = splitTerm k n a := by
  have haBounds := mem_A_iff.mp ha
  have hdlt : k + 1 - a < a := by omega
  let L : SimpleGraph (Fin a) := cyclicDegreeGraph (k + 1 - a) a
  let R : SimpleGraph (Fin (n - a)) := ⊥
  have hdisjoint :
      Disjoint (L ⊕g R) (completeBipartiteGraph (Fin a) (Fin (n - a))) :=
    sum_disjoint_completeBipartiteGraph L R
  have hcomplete :
      (completeBipartiteGraph (Fin a) (Fin (n - a))).edgeSet.ncard =
        a * (n - a) := by
    rw [ncard_edgeSet_eq_card_edgeFinset,
      completeBipartiteGraph_card_edgeFinset]
  rw [← ncard_edgeSet_eq_card_edgeFinset]
  change
    ((L ⊕g R) ⊔ completeBipartiteGraph (Fin a) (Fin (n - a))).edgeSet.ncard =
      splitTerm k n a
  rw [SimpleGraph.edgeSet_sup,
    Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr hdisjoint),
    ncard_edgeSet_sum_eq]
  change
    (cyclicDegreeGraph (k + 1 - a) a).edgeSet.ncard +
        (⊥ : SimpleGraph (Fin (n - a))).edgeSet.ncard +
      (completeBipartiteGraph (Fin a) (Fin (n - a))).edgeSet.ncard =
      splitTerm k n a
  rw [cyclicDegreeGraph_ncard_edgeSet_eq (k + 1 - a) a hdlt,
    hcomplete]
  simp [splitTerm, Nat.mul_comm, Nat.add_comm]

/-- The same exact count, displayed in the notation used in the manuscript. -/
theorem splitGraph_card_edgeFinset_eq
    (k n a : ℕ) [NeZero a] (ha : a ∈ A k) :
    (splitGraph k n a).edgeFinset.card =
      a * (n - a) + (a * (k + 1 - a)) / 2 := by
  simpa [splitTerm] using splitGraph_card_edgeFinset_eq_splitTerm k n a ha

@[simp] theorem splitGraph_adj_left {k n a : ℕ} [NeZero a] {x x' : Fin a} :
    (splitGraph k n a).Adj (.inl x) (.inl x') ↔
      (cyclicDegreeGraph (k + 1 - a) a).Adj x x' := by
  simp [splitGraph]

@[simp] theorem splitGraph_adj_right {k n a : ℕ} [NeZero a]
    {y y' : Fin (n - a)} :
    ¬(splitGraph k n a).Adj (.inr y) (.inr y') := by
  simp [splitGraph]

@[simp] theorem splitGraph_adj_cross {k n a : ℕ} [NeZero a]
    {x : Fin a} {y : Fin (n - a)} :
    (splitGraph k n a).Adj (.inl x) (.inr y) := by
  simp [splitGraph]

/-- A right-side vertex is adjacent to exactly all `a` left-side vertices. -/
theorem splitGraph_neighborFinset_right {k n a : ℕ} [NeZero a]
    (y : Fin (n - a)) :
    (splitGraph k n a).neighborFinset (.inr y) =
      Finset.univ.map Function.Embedding.inl := by
  classical
  ext z
  cases z with
  | inl x =>
      have h : (splitGraph k n a).Adj (.inr y) (.inl x) :=
        (splitGraph_adj_cross (k := k) (n := n) (a := a) (x := x) (y := y)).symm
      simpa using h
  | inr z => simp

@[simp] theorem splitGraph_degree_right {k n a : ℕ} [NeZero a]
    (y : Fin (n - a)) :
    (splitGraph k n a).degree (.inr y) = a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    splitGraph_neighborFinset_right, Finset.card_map, Finset.card_univ,
    Fintype.card_fin]

end Split

end Erdos767
