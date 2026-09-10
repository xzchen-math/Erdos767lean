import Erdos767.Chapter5
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.List.Cycle

/-!
# Chapter 5 deductions under the Route-A literature interface

This file states exact extremal conclusions as an upper bound together with
an actual graph attaining it.  The witness type is quantified explicitly, so
the split construction need not be artificially relabeled onto `Fin n`.
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

/-- Some `n`-vertex `PF_ell`-free graph has exactly `B` edges. -/
def AttainedEdgeCount (ell n B : ℕ) : Prop :=
  ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U)
    (H : SimpleGraph U) (_ : DecidableRel H.Adj),
      Fintype.card U = n ∧ PathFanFree H ell ∧ H.edgeFinset.card = B

/-- `B` is an exact universal edge bound: every admissible graph has at
most `B` edges, and one admissible graph attains `B`. -/
def ExactUniversalEdgeBound (ell n B : ℕ) : Prop :=
  UniversalEdgeBound.{u} ell n B ∧ AttainedEdgeCount ell n B

local instance routeAChapter5DecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

/-! ## Rich-host deductions used in the base lemma -/

/-- Consecutive elements of the duplicate-free cyclic support are adjacent.
The last element is followed by the first, so this is the literal successor
map used in `claim:ext-rich-host2`. -/
theorem CycleWitness.next_adj
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (C : CycleWitness G)
    (x : V) (hx : x ∈ C.walk.support.dropLast) :
    G.Adj x (C.walk.support.dropLast.next x hx) := by
  let L := C.walk.support.dropLast
  have hLlen : L.length = C.walk.length := by
    dsimp [L]
    rw [List.length_dropLast, C.walk.length_support]
    omega
  have hLn : L.Nodup := C.isCycle.nodup_dropLast_support
  let i := L.idxOf x
  have hi : i < L.length := List.idxOf_lt_length_of_mem hx
  have hxget : L[i] = x := List.getElem_idxOf hi
  have hLpos : 0 < L.length := by omega
  have hmodlt : (i + 1) % L.length < L.length := Nat.mod_lt _ hLpos
  rw [List.next_eq_getElem hx]
  change G.Adj x (L[(i + 1) % L.length]'hmodlt)
  have hxi : C.walk.getVert i = x := by
    rw [← hxget]
    simp [L, List.getElem_dropLast, C.walk.support_getElem_eq_getVert]
  have hadjTarget : G.Adj (C.walk.getVert i)
      (L[(i + 1) % L.length]'hmodlt) := by
    by_cases hilast : i + 1 < L.length
    · have hiC : i < C.walk.length := by omega
      have hmodC : (i + 1) % C.walk.length = i + 1 :=
        Nat.mod_eq_of_lt (by omega)
      simpa [L, List.getElem_dropLast, C.walk.support_getElem_eq_getVert,
        hmodC] using C.walk.adj_getVert_succ hiC
    · have hiEq : i + 1 = L.length := by omega
      have hiC : i < C.walk.length := by omega
      have hadj := C.walk.adj_getVert_succ hiC
      rw [hiEq, hLlen] at hadj
      simpa [L, List.getElem_dropLast, C.walk.support_getElem_eq_getVert,
        hiEq, hLlen] using hadj
  exact hxi ▸ hadjTarget

/-- Removing the duplicated terminal vertex from a cycle support does not
change its vertex finset. -/
theorem CycleWitness.dropLast_support_toFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (C : CycleWitness G) :
    C.walk.support.dropLast.toFinset = C.vertexFinset := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hx' : x ∈ C.walk.support.dropLast := by simpa using hx
    have : x ∈ C.walk.support := List.mem_of_mem_dropLast hx'
    simpa [CycleWitness.vertexFinset] using this
  · have hcardL : C.walk.support.dropLast.toFinset.card = C.length := by
      rw [List.toFinset_card_of_nodup C.isCycle.nodup_dropLast_support]
      rw [List.length_dropLast, C.walk.length_support]
      simp [CycleWitness.length]
    have hcardC : C.vertexFinset.card = C.length := C.card_vertexFinset
    intro x hx
    by_contra hnot
    have hproper : C.walk.support.dropLast.toFinset ⊂ C.vertexFinset := by
      refine ⟨?_, ?_⟩
      · intro y hy
        have hy' : y ∈ C.walk.support.dropLast := by simpa using hy
        have : y ∈ C.walk.support := List.mem_of_mem_dropLast hy'
        simpa [CycleWitness.vertexFinset] using this
      · intro heq
        exact hnot (heq hx)
    have := Finset.card_lt_card hproper
    omega

/-- Claim `claim:ext-rich-host1`: in the exterior-rich case the exceptional
Ma--Ning hosts are ruled out by the verified low-degree lemma, leaving the
canonical `W` host. -/
theorem ext_rich_host1_of_literature
    (lit : LiteratureTheorems.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G) {k : ℕ}
    (hk : 2 ≤ k)
    (hnUpper : Fintype.card V ≤ (5 * k + 2) / 2)
    (h2c : IsTwoConnected G) (hlongest : IsLongestCycle C)
    (hc10 : 10 ≤ C.length) (hcn : C.length < Fintype.card V)
    (hmin : (k + 1) / 2 + 1 ≤ G.minDegree)
    (hrich :
      (C.length / 2 - 1) * (Fintype.card V - C.length) <
        (G.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
          (edgesBetween G (Finset.univ \ C.vertexFinset)
            C.vertexFinset).card) :
    IsSubgraphOfW G (Fintype.card V) (C.length / 2) C.length := by
  rcases lit.maNingExteriorStability G C h2c hlongest hc10 hcn hrich with
    hW | ⟨hcOdd, hExceptional⟩
  · exact hW
  · rcases hExceptional with ⟨H, instHAdj, hGH, hFamily⟩
    rcases exceptional_low_degree_or_W (G := H) hcn hFamily with
      hHW | ⟨v, hvLow⟩
    · rcases hHW with ⟨W, hW, hHW⟩
      exact ⟨W, hW, hGH.trans hHW⟩
    · have hcmod : C.length % 2 = 1 := Nat.odd_iff.mp hcOdd
      have hkFive : 5 ≤ k := by omega
      have hfour : 4 ≤ G.minDegree := by omega
      have hdegreeMono : G.degree v ≤ H.degree v :=
        G.degree_le_of_le (v := v) hGH
      have hminDegree : G.minDegree ≤ G.degree v :=
        G.minDegree_le_degree v
      omega

/-- Claim `claim:ext-rich-host2`.  The successor map of the cycle gives an
injection from `U ∩ V(C)` into `S ∩ V(C)`.  Exact partition arithmetic then
forces every vertex of `S` onto the cycle and leaves at most one vertex of
`T` outside it.  The returned witnesses retain all host data needed later. -/
theorem ext_rich_host2
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G)
    (hW : IsSubgraphOfW G (Fintype.card V) (C.length / 2) C.length) :
    ∃ (H : SimpleGraph V) (S T U : Finset V),
      G ≤ H ∧
      Disjoint S T ∧ Disjoint S U ∧ Disjoint T U ∧
      S ∪ T ∪ U = Finset.univ ∧
      S.card = C.length / 2 ∧
      T.card = C.length - 2 * (C.length / 2) + 1 ∧
      U.card = Fintype.card V - C.length + C.length / 2 - 1 ∧
      (∀ x y : V,
        H.Adj x y ↔
          x ≠ y ∧
            ((x ∈ S ∪ T ∧ y ∈ S ∪ T) ∨
             (x ∈ U ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ U))) ∧
      S ⊆ C.vertexFinset ∧
      (T \ C.vertexFinset).card ≤ 1 := by
  rcases hW with ⟨H, hH, hGH⟩
  rcases hH with ⟨hn, hspos, hsupper, hsize,
    S, T, U, hST, hSU, hTU, hpart, hScard, hTcard, hUcard, hAdj⟩
  let L := C.walk.support.dropLast
  have hLC : L.toFinset = C.vertexFinset := C.dropLast_support_toFinset
  have hLn : L.Nodup := C.isCycle.nodup_dropLast_support
  let UC := U ∩ C.vertexFinset
  let SC := S ∩ C.vertexFinset
  let TC := T ∩ C.vertexFinset
  let f : (↥UC) → (↥SC) := fun u => by
    have huMem := u.property
    change (u : V) ∈ U ∩ C.vertexFinset at huMem
    have huUC : (u : V) ∈ U ∧ (u : V) ∈ C.vertexFinset :=
      Finset.mem_inter.mp huMem
    have huC : (u : V) ∈ C.vertexFinset := huUC.2
    have huL : (u : V) ∈ L := by
      rw [← hLC] at huC
      simpa using huC
    let v := L.next (u : V) huL
    have huvG : G.Adj (u : V) v := C.next_adj (u : V) huL
    have huvH : H.Adj (u : V) v := hGH huvG
    have hvC : v ∈ C.vertexFinset := by
      rw [← hLC]
      simpa [v] using List.next_mem L (u : V) huL
    have hvS : v ∈ S := by
      rcases (hAdj (u : V) v).mp huvH with ⟨_, hcases⟩
      rcases hcases with hboth | huvs | hsuv
      · rcases Finset.mem_union.mp hboth.1 with huS | huT
        · exact (Finset.disjoint_left.mp hSU huS huUC.1).elim
        · exact (Finset.disjoint_left.mp hTU huT huUC.1).elim
      · exact huvs.2
      · exact (Finset.disjoint_left.mp hSU hsuv.1 huUC.1).elim
    exact ⟨v, Finset.mem_inter.mpr ⟨hvS, hvC⟩⟩
  let nextMap : (↥L.toFinset) → (↥L.toFinset) := fun z =>
    ⟨L.next (z : V) (by
        have hz := z.property
        change (z : V) ∈ L.toFinset at hz
        exact List.mem_toFinset.mp hz),
      by
        apply List.mem_toFinset.mpr
        apply List.next_mem⟩
  let prevMap : (↥L.toFinset) → (↥L.toFinset) := fun z =>
    ⟨L.prev (z : V) (by
        have hz := z.property
        change (z : V) ∈ L.toFinset at hz
        exact List.mem_toFinset.mp hz),
      by
        apply List.mem_toFinset.mpr
        apply List.prev_mem⟩
  have hleft : Function.LeftInverse prevMap nextMap := by
    intro z
    apply Subtype.ext
    apply List.prev_next L hLn (z : V)
    have hz := z.property
    change (z : V) ∈ L.toFinset at hz
    exact List.mem_toFinset.mp hz
  have hnextInjective : Function.Injective nextMap := hleft.injective
  have hfInjective : Function.Injective f := by
    intro a b hab
    have haMem := a.property
    have hbMem := b.property
    change (a : V) ∈ U ∩ C.vertexFinset at haMem
    change (b : V) ∈ U ∩ C.vertexFinset at hbMem
    have haUC : (a : V) ∈ U ∧ (a : V) ∈ C.vertexFinset :=
      Finset.mem_inter.mp haMem
    have hbUC : (b : V) ∈ U ∧ (b : V) ∈ C.vertexFinset :=
      Finset.mem_inter.mp hbMem
    have haC : (a : V) ∈ C.vertexFinset := haUC.2
    have hbC : (b : V) ∈ C.vertexFinset := hbUC.2
    have haL : (a : V) ∈ L := by
      rw [← hLC] at haC
      simpa using haC
    have hbL : (b : V) ∈ L := by
      rw [← hLC] at hbC
      simpa using hbC
    let aL : ↥L.toFinset := ⟨a, by simpa using haL⟩
    let bL : ↥L.toFinset := ⟨b, by simpa using hbL⟩
    have hmaps : nextMap aL = nextMap bL := by
      apply Subtype.ext
      have hnext := congrArg Subtype.val hab
      dsimp [f] at hnext
      simpa [nextMap, aL, bL] using hnext
    have habL := hnextInjective hmaps
    apply Subtype.ext
    have hval := congrArg Subtype.val habL
    simpa [aL, bL] using hval
  have hUCleSC : UC.card ≤ SC.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hfInjective
  have hdecomp : C.vertexFinset = SC ∪ TC ∪ UC := by
    ext x
    simp only [SC, TC, UC, Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hxC
      have hxU : x ∈ S ∪ T ∪ U := by rw [hpart]; simp
      rcases Finset.mem_union.mp hxU with hxST | hxU
      · rcases Finset.mem_union.mp hxST with hxS | hxT
        · exact Or.inl (Or.inl ⟨hxS, hxC⟩)
        · exact Or.inl (Or.inr ⟨hxT, hxC⟩)
      · exact Or.inr ⟨hxU, hxC⟩
    · intro hx
      rcases hx with hSCT | hUC
      · rcases hSCT with hSC | hTC
        · exact hSC.2
        · exact hTC.2
      · exact hUC.2
  have hSCTC : Disjoint SC TC := by
    exact hST.mono (by simpa [SC] using Finset.inter_subset_left)
      (by simpa [TC] using Finset.inter_subset_left)
  have hSCUC : Disjoint SC UC := by
    exact hSU.mono (by simpa [SC] using Finset.inter_subset_left)
      (by simpa [UC] using Finset.inter_subset_left)
  have hTCUC : Disjoint TC UC := by
    exact hTU.mono (by simpa [TC] using Finset.inter_subset_left)
      (by simpa [UC] using Finset.inter_subset_left)
  have hCardDecomp : C.vertexFinset.card = SC.card + TC.card + UC.card := by
    rw [hdecomp, Finset.card_union_of_disjoint]
    · rw [Finset.card_union_of_disjoint hSCTC]
    · exact Finset.disjoint_union_left.mpr ⟨hSCUC, hTCUC⟩
  have hTCleT : TC.card ≤ T.card := Finset.card_le_card
    (by simpa [TC] using Finset.inter_subset_left)
  have hCycleTC : C.length ≤ 2 * SC.card + TC.card := by
    rw [← C.card_vertexFinset]
    omega
  have hTauLeTwo : C.length - 2 * (C.length / 2) + 1 ≤ 2 := by omega
  have hSsubset : S ⊆ C.vertexFinset := by
    intro x hxS
    by_contra hxC
    have hSCproper : SC.card ≤ S.card - 1 := by
      have hstrict : SC ⊂ S := by
        refine ⟨?_, ?_⟩
        · simpa [SC] using Finset.inter_subset_left
        · intro hrev
          have hxSC := hrev hxS
          change x ∈ S ∩ C.vertexFinset at hxSC
          exact hxC (Finset.mem_inter.mp hxSC).2
      have := Finset.card_lt_card hstrict
      omega
    have hTCleT' : TC.card ≤ C.length - 2 * (C.length / 2) + 1 := by
      rw [← hTcard]
      exact hTCleT
    omega
  have hSCleS : SC.card ≤ S.card := Finset.card_le_card
    (by simpa [SC] using Finset.inter_subset_left)
  have hSleSC : S.card ≤ SC.card := Finset.card_le_card (by
    intro x hxS
    change x ∈ S ∩ C.vertexFinset
    exact Finset.mem_inter.mpr ⟨hxS, hSsubset hxS⟩)
  have hSCeq : SC.card = S.card := by omega
  have hTCcardLower : T.card - 1 ≤ TC.card := by
    rw [hScard] at hSCeq
    rw [hSCeq] at hCycleTC
    rw [hTcard]
    omega
  have hTdiff : (T \ C.vertexFinset).card ≤ 1 := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_comm]
    change T.card - TC.card ≤ 1
    omega
  exact ⟨H, S, T, U, hGH, hST, hSU, hTU, hpart,
    hScard, hTcard, hUcard, hAdj, hSsubset, hTdiff⟩

/-- The custom crossing-edge finset agrees with Mathlib's bipartite
`between` graph. -/
theorem edgesBetween_eq_between_edgeFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (X Y : Finset V) (_hXY : Disjoint X Y) :
    edgesBetween G X Y =
      (G.between (X : Set V) (Y : Set V)).edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [edgesBetween, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.between_adj]
      constructor
      · rintro ⟨hxy, a, haX, b, hbY, hab⟩
        have habEnds : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
          rcases (Sym2.eq_iff.mp hab) with h | h
          · exact Or.inl ⟨h.1.symm, h.2.symm⟩
          · exact Or.inr ⟨h.2.symm, h.1.symm⟩
        rcases habEnds with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hxy, Or.inl ⟨haX, hbY⟩⟩
        · exact ⟨hxy, Or.inr ⟨hbY, haX⟩⟩
      · rintro ⟨hxy, hparts⟩
        rcases hparts with ⟨hxX, hyY⟩ | ⟨hxY, hyX⟩
        · exact ⟨hxy, x, hxX, y, hyY, rfl⟩
        · exact ⟨hxy, y, hyX, x, hxY, Sym2.eq_swap⟩

/-- Crossing edges are counted once by summing the numbers of neighbors on
the opposite side. -/
theorem edgesBetween_card_eq_sum_neighborsIn
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (X Y : Finset V) (hXY : Disjoint X Y) :
    (edgesBetween G X Y).card =
      ∑ x ∈ X, (neighborsIn G x Y).card := by
  let K := G.between (X : Set V) (Y : Set V)
  have hBip : K.IsBipartiteWith (X : Set V) (Y : Set V) :=
    G.between_isBipartiteWith (by simpa using hXY)
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hBip
  rw [edgesBetween_eq_between_edgeFinset X Y hXY]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro x hxX
  rw [← K.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp [K, neighborsIn, SimpleGraph.between_adj, hxX,
    Finset.disjoint_left.mp hXY hxX, and_comm]

/-- The tail of a cycle is a path containing exactly the cycle vertices. -/
theorem CycleWitness.tail_support_toFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (C : CycleWitness G) :
    C.walk.tail.support.toFinset = C.vertexFinset := by
  have hperm := C.walk.support_tail_perm_support_dropLast
  rw [C.walk.support_dropLast C.isCycle.not_nil] at hperm
  rw [← C.dropLast_support_toFinset]
  ext x
  simpa using hperm.mem_iff

/-- A vertex outside a cycle in a `PF_(k+2)`-free graph has at most `k+1`
neighbors on that cycle. -/
theorem outside_cycle_neighbor_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hfree : PathFanFree G (k + 2)) (C : CycleWitness G)
    (z : V) (hz : z ∉ C.vertexFinset) :
    (neighborsIn G z C.vertexFinset).card ≤ k + 1 := by
  by_contra hlarge
  apply hfree
  refine ⟨z, C.walk.snd, C.base, C.walk.tail,
    C.isCycle.isPath_tail, ?_, ?_⟩
  · intro hzTail
    apply hz
    rw [← C.tail_support_toFinset]
    simpa using hzTail
  · have heq : walkNeighbors z C.walk.tail =
        neighborsIn G z C.vertexFinset := by
      unfold walkNeighbors neighborsIn
      rw [C.tail_support_toFinset]
    rw [heq]
    omega

/-- Finite averaging in the form needed for the rich-exterior claim. -/
theorem exists_large_neighborsIn_of_edgesBetween
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (X Y : Finset V) (q : ℕ)
    (hlarge : (q - 1) * X.card < (edgesBetween G X Y).card)
    (hXY : Disjoint X Y) :
    ∃ z ∈ X, q ≤ (neighborsIn G z Y).card := by
  rw [edgesBetween_card_eq_sum_neighborsIn X Y hXY] at hlarge
  by_cases hq0 : q = 0
  · obtain ⟨z, hzX, hzpos⟩ := Finset.sum_pos_iff.mp (by
      simpa [hq0] using hlarge)
    exact ⟨z, hzX, by omega⟩
  by_contra hnone
  push Not at hnone
  have hsum : (∑ z ∈ X, (neighborsIn G z Y).card) ≤
      ∑ _z ∈ X, (q - 1) := by
    apply Finset.sum_le_sum
    intro z hz
    have := hnone z hz
    omega
  have hsum' : (∑ z ∈ X, (neighborsIn G z Y).card) ≤
      (q - 1) * X.card := by
    simpa [Nat.mul_comm] using hsum
  exact (not_lt_of_ge hsum' hlarge)

/-- The short final step of `claim:ext-rich-edge-bound`, isolated from its
host-edge accounting. -/
theorem halfCycle_mem_A_of_large_outside_attachment
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hfree : PathFanFree G (k + 2)) (C : CycleWitness G)
    (hcycleLower : 2 * ((k + 1) / 2) + 2 ≤ C.length)
    (hattachment : ∃ z ∈ Finset.univ \ C.vertexFinset,
      C.length / 2 ≤ (neighborsIn G z C.vertexFinset).card) :
    C.length / 2 ∈ A k := by
  rw [mem_A_iff]
  constructor
  · omega
  · rcases hattachment with ⟨z, hzOut, hzDegree⟩
    have hzNot : z ∉ C.vertexFinset := (Finset.mem_sdiff.mp hzOut).2
    have hupper := outside_cycle_neighbor_bound hfree C z hzNot
    omega

/-- Claim `claim:ext-rich-edge-bound` in full.  The verified host occupancy
makes the exterior induced graph empty; crossing-edge averaging supplies a
vertex with `q` cycle neighbors, and `PF_(k+2)`-freeness gives `q≤k+1`. -/
theorem ext_rich_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hfree : PathFanFree G (k + 2)) (C : CycleWitness G)
    (hcycleLower : 2 * ((k + 1) / 2) + 2 ≤ C.length)
    (hW : IsSubgraphOfW G (Fintype.card V) (C.length / 2) C.length)
    (hrich :
      (C.length / 2 - 1) * (Fintype.card V - C.length) <
        (G.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
          (edgesBetween G (Finset.univ \ C.vertexFinset)
            C.vertexFinset).card) :
    C.length / 2 ∈ A k := by
  rcases ext_rich_host2 C hW with
    ⟨H, S, T, U, hGH, hST, hSU, hTU, hpart,
      hScard, hTcard, hUcard, hAdj, hSsubset, hTdiff⟩
  let X := Finset.univ \ C.vertexFinset
  have hInduceBot : G.induce (↑X : Set V) = ⊥ := by
    ext x y
    constructor
    · intro hxy
      have hxOut : (x : V) ∉ C.vertexFinset := by
        have hx := x.property
        change (x : V) ∈ X at hx
        exact (Finset.mem_sdiff.mp hx).2
      have hyOut : (y : V) ∉ C.vertexFinset := by
        have hy := y.property
        change (y : V) ∈ X at hy
        exact (Finset.mem_sdiff.mp hy).2
      have hxyH : H.Adj (x : V) (y : V) := hGH hxy
      rcases (hAdj (x : V) (y : V)).mp hxyH with ⟨hxyne, hcases⟩
      rcases hcases with hSTcase | hUScase | hSUcase
      · have hxT : (x : V) ∈ T := by
          rcases Finset.mem_union.mp hSTcase.1 with hxS | hxT
          · exact (hxOut (hSsubset hxS)).elim
          · exact hxT
        have hyT : (y : V) ∈ T := by
          rcases Finset.mem_union.mp hSTcase.2 with hyS | hyT
          · exact (hyOut (hSsubset hyS)).elim
          · exact hyT
        have hxDiff : (x : V) ∈ T \ C.vertexFinset :=
          Finset.mem_sdiff.mpr ⟨hxT, hxOut⟩
        have hyDiff : (y : V) ∈ T \ C.vertexFinset :=
          Finset.mem_sdiff.mpr ⟨hyT, hyOut⟩
        have hxyEq : (x : V) = (y : V) := by
          by_contra hne
          have htwo : 2 ≤ (T \ C.vertexFinset).card := by
            have hsub : ({(x : V), (y : V)} : Finset V) ⊆
                T \ C.vertexFinset := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hxDiff
              · exact hyDiff
            have hcardPair : ({(x : V), (y : V)} : Finset V).card = 2 := by
              simp [hne]
            rw [← hcardPair]
            exact Finset.card_le_card hsub
          omega
        exact (hxyne hxyEq).elim
      · exact (hyOut (hSsubset hUScase.2)).elim
      · exact (hxOut (hSsubset hSUcase.1)).elim
    · simp
  have hInduceZero :
      (G.induce (↑X : Set V)).edgeFinset.card = 0 := by
    have hedgeEmpty : (G.induce (↑X : Set V)).edgeFinset = ∅ :=
      SimpleGraph.edgeFinset_eq_empty.mpr hInduceBot
    rw [hedgeEmpty]
    rfl
  have hXcard : X.card = Fintype.card V - C.length := by
    dsimp [X]
    rw [Finset.card_sdiff]
    simp [C.card_vertexFinset]
  have hCrossRich :
      (C.length / 2 - 1) * X.card <
        (edgesBetween G X C.vertexFinset).card := by
    calc
      (C.length / 2 - 1) * X.card =
          (C.length / 2 - 1) * (Fintype.card V - C.length) := by
        rw [hXcard]
      _ < (edgesBetween G X C.vertexFinset).card := by
        dsimp [X] at hInduceZero ⊢
        rw [hInduceZero] at hrich
        simpa only [zero_add] using hrich
  have hDisjoint : Disjoint X C.vertexFinset := by
    apply Finset.disjoint_left.mpr
    intro x hxX hxC
    exact (Finset.mem_sdiff.mp hxX).2 hxC
  obtain ⟨z, hzX, hzDegree⟩ :=
    exists_large_neighborsIn_of_edgesBetween X C.vertexFinset
      (C.length / 2) hCrossRich hDisjoint
  apply halfCycle_mem_A_of_large_outside_attachment hfree C hcycleLower
  exact ⟨z, hzX, hzDegree⟩

/-- The nearly regular construction attains `t_k(n)`. -/
theorem attained_t {k n : ℕ} (hn : k + 2 ≤ n) :
    AttainedEdgeCount (k + 2) n (t k n) := by
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  refine ⟨Fin n, inferInstance, inferInstance, nearlyRegularGraph k n,
    inferInstance, ?_, nearlyRegularGraph_pathFanFree k n (by omega), ?_⟩
  · simp
  · exact nearlyRegularGraph_card_edgeFinset_eq_t k n hn

/-- Every admissible split parameter gives an attained edge count. -/
theorem attained_splitTerm {k n a : ℕ} (hk : 1 ≤ k)
    (hn : k + 2 ≤ n) (ha : a ∈ A k) :
    AttainedEdgeCount (k + 2) n (splitTerm k n a) := by
  have haBounds := mem_A_iff.mp ha
  have hapos : 0 < a := by omega
  have han : a ≤ n := haBounds.2.trans (by omega)
  letI : NeZero a := ⟨Nat.ne_of_gt hapos⟩
  refine ⟨Fin a ⊕ Fin (n - a), inferInstance, inferInstance,
    splitGraph k n a, inferInstance, ?_,
    splitGraph_pathFanFree k n a hk ha, ?_⟩
  · simp [Fintype.card_sum]
    omega
  · exact splitGraph_card_edgeFinset_eq_splitTerm k n a ha

/-- A maximizing split construction attains `p_k(n)`. -/
theorem attained_p {k n : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    AttainedEdgeCount (k + 2) n (p k n) := by
  obtain ⟨a, ha, hmax⟩ := exists_maximizing_splitTerm k n
  have hattain := attained_splitTerm hk hn ha
  simpa [hmax] using hattain

/-- The better of the two manuscript constructions attains `h_k(n)`. -/
theorem attained_h {k n : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    AttainedEdgeCount (k + 2) n (h k n) := by
  rw [h_eq_max hn]
  rcases max_cases (t k n) (p k n) with ⟨ht, _⟩ | ⟨hp, _⟩
  · rw [ht]
    exact attained_t hn
  · rw [hp]
    exact attained_p hk hn

/-- The terminal split construction (`a=k+1`) attains the linear count. -/
theorem attained_terminal {k n : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    AttainedEdgeCount (k + 2) n ((k + 1) * (n - k - 1)) := by
  have hattain := attained_splitTerm hk hn (top_mem_A k)
  convert hattain using 1
  simp [splitTerm]
  omega

/-- An upper proof of the base lemma plus the already verified lower
construction yields the exact base-range statement. -/
theorem exact_base_of_upper {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hupper : UniversalEdgeBound.{u} (k + 2) n (h k n)) :
    ExactUniversalEdgeBound.{u} (k + 2) n (h k n) :=
  ⟨hupper, attained_h (by omega) hn⟩

/-- The checked terminal induction, combined with the terminal split graph,
gives the exact terminal-range result from the base endpoint. -/
theorem exact_terminal_of_base
    {k n : ℕ} (hk : 2 ≤ k) (hn : (5 * k + 2) / 2 ≤ n)
    (hbase : UniversalEdgeBound.{u} (k + 2) ((5 * k + 2) / 2)
      (h k ((5 * k + 2) / 2))) :
    ExactUniversalEdgeBound.{u} (k + 2) n
      ((k + 1) * (n - k - 1)) := by
  refine ⟨terminal_bound hk hn hbase, ?_⟩
  apply attained_terminal (by omega)
  have : k + 2 ≤ (5 * k + 2) / 2 := by omega
  exact this.trans hn

/-- The exceptional initial value `g_1(3)=3`. -/
theorem exact_k_one_three :
    ExactUniversalEdgeBound.{u} 3 3 3 := by
  constructor
  · intro U instU instDec H instAdj hcard hfree
    have hedge := H.card_edgeFinset_le_card_choose_two
    simpa [hcard] using hedge
  · refine ⟨Fin 3, inferInstance, inferInstance,
      (⊤ : SimpleGraph (Fin 3)), inferInstance, by simp, ?_, ?_⟩
    · apply pathFanFree_of_forall_degree_lt
      intro x
      simp
    · simpa using
        (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 3))

/-- Pósa's cited theorem and the `a=2` split construction give the complete
`k=1`, `n≥4` branch of the manuscript's main theorem. -/
theorem exact_k_one_of_four_le (lit : LiteratureTheorems.{u})
    {n : ℕ} (hn : 4 ≤ n) :
    ExactUniversalEdgeBound.{u} 3 n (2 * n - 4) := by
  constructor
  · intro U instU instDec H instAdj hcard hfree
    have hposa := lit.posaChordedCycle H (by omega) hfree
    simpa [hcard] using hposa
  · have hattain := attained_splitTerm
      (k := 1) (n := n) (a := 2) (by decide) (by omega) (top_mem_A 1)
    convert hattain using 1
    simp [splitTerm]
    omega

/-- The full `k=1` conclusion, split at the manuscript's exceptional
three-vertex value. -/
theorem main_k_one_of_three_le (lit : LiteratureTheorems.{u})
    {n : ℕ} (hn : 3 ≤ n) :
    if n = 3 then ExactUniversalEdgeBound.{u} 3 n 3
    else ExactUniversalEdgeBound.{u} 3 n (2 * n - 4) := by
  split_ifs with hthree
  · subst n
    exact exact_k_one_three
  · exact exact_k_one_of_four_le lit (by omega)

/-- The upper-bound content of manuscript Lemma `lem:base`, uniformly over
its full parameter range. -/
def BaseRangeUpper : Prop :=
  ∀ (k n : ℕ), 2 ≤ k → k + 2 ≤ n → n ≤ (5 * k + 2) / 2 →
    UniversalEdgeBound.{u} (k + 2) n (h k n)

/-- Once `lem:base` is available, all remaining induction and lower-bound
work yields the complete `k≥2` piece of the main theorem.  This theorem makes
the single remaining dependency explicit rather than hiding it. -/
theorem main_k_ge_two_of_baseRangeUpper
    (hbaseRange : BaseRangeUpper.{u})
    {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n) :
    if n < (5 * k + 2) / 2 then
      ExactUniversalEdgeBound.{u} (k + 2) n (h k n)
    else
      ExactUniversalEdgeBound.{u} (k + 2) n
        ((k + 1) * (n - k - 1)) := by
  split_ifs with hsmall
  · exact exact_base_of_upper hk hn
      (hbaseRange k n hk hn (by omega))
  · have hnTerminal : (5 * k + 2) / 2 ≤ n := by omega
    have hkBase : k + 2 ≤ (5 * k + 2) / 2 := by omega
    have hendpoint := hbaseRange k ((5 * k + 2) / 2)
      hk hkBase (le_rfl)
    exact exact_terminal_of_base hk hnTerminal hendpoint

end

end Erdos767
