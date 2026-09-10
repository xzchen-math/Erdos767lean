import Erdos767.Chapter3
import Erdos767.Chapter4RouteA
import Erdos767.SplitPathFan
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Chapter 5: verified graph interfaces and the terminal induction

This file formalizes the parts of Chapter 5 whose prerequisites are already
available without importing any unproved literature theorem.  In particular,
it proves the cycle-degree observation, functoriality of path-fans under graph
embeddings, the longest-path low-degree lemma, exact edge accounting under
vertex deletion, and the complete induction used in `lem:terminal`.

The theorem `terminal_bound` exposes `lem:base` as its only premise.  This is
intentional: the manuscript proof of `lem:base` depends on the Chapter 4
Dirac, Ma--Ning, Fan--Lv--Wang, and Erdős--Gallai inputs, none of which is in
Mathlib at the pinned version.
-/

namespace Erdos767

open SimpleGraph

universe u w

/-- Lemma `lem:cycle-degree` in the centered-cycle representation used by
`GraphBasics.lean`: the displayed number is exactly the degree of the center
inside the vertices of the cycle. -/
theorem cycle_degree {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hfree : PathFanFree G (k + 2))
    (C : CenteredCycle G) :
    (walkNeighbors C.center C.spine).card ≤ k + 1 := by
  by_contra hlarge
  apply hfree
  refine ⟨C.center, C.start, C.finish, C.spine, C.spine_isPath,
    C.center_not_mem, ?_⟩
  omega

/-- Rotate a cycle to `x` and remove both occurrences of `x`, producing
the center-deleted path used by `CenteredCycle`. -/
noncomputable def CycleWitness.centeredAt
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (C : CycleWitness G) (x : V)
    (hx : x ∈ C.vertexFinset) : CenteredCycle G := by
  have hxSupport : x ∈ C.walk.support := by
    simpa [CycleWitness.vertexFinset] using hx
  let r : G.Walk x x := C.walk.rotate x hxSupport
  have hr : r.IsCycle := C.isCycle.rotate hxSupport
  have htailNotNil : ¬ r.tail.Nil := by
    intro hnil
    have htailLength : r.tail.length + 1 = r.length :=
      r.length_tail_add_one hr.not_nil
    have hzero : r.tail.length = 0 := hnil.length_eq_zero
    have hthree : 3 ≤ r.length := hr.three_le_length
    omega
  have hspinePath : (r.tail.dropLast).IsPath :=
    hr.isPath_tail.dropLast
  have hspineNotNil : ¬ r.tail.dropLast.Nil := by
    intro hnil
    have htailLength : r.tail.length + 1 = r.length :=
      r.length_tail_add_one hr.not_nil
    have hdropLength : r.tail.dropLast.length + 1 = r.tail.length :=
      r.tail.length_dropLast_add_one htailNotNil
    have hzero : r.tail.dropLast.length = 0 := hnil.length_eq_zero
    have hthree : 3 ≤ r.length := hr.three_le_length
    omega
  have hxNotSpine : x ∉ r.tail.dropLast.support := by
    have hnodupTail : r.tail.support.Nodup := hr.isPath_tail.support_nodup
    have hsupport : r.tail.dropLast.support ++ [x] = r.tail.support :=
      r.tail.support_dropLast_concat htailNotNil
    have hnodupAppend : (r.tail.dropLast.support ++ [x]).Nodup := by
      rw [hsupport]
      exact hnodupTail
    have hdisjoint := (List.nodup_append'.mp hnodupAppend).2.2
    simpa using hdisjoint
  have hstartFinish : r.snd ≠ r.tail.penultimate := by
    intro heq
    exact hspineNotNil ((hspinePath.nil_iff_eq).2 heq)
  exact
    { center := x
      start := r.snd
      finish := r.tail.penultimate
      spine := r.tail.dropLast
      spine_isPath := hspinePath
      center_not_mem := hxNotSpine
      start_ne_finish := hstartFinish
      adj_start := r.adj_snd hr.not_nil
      adj_finish := (r.tail.adj_penultimate htailNotNil).symm }

/-- The center-deleted spine has exactly the neighbors of `x` lying on
the original cycle. -/
theorem CycleWitness.walkNeighbors_centeredAt
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (C : CycleWitness G) (x : V)
    (hx : x ∈ C.vertexFinset) :
    walkNeighbors x (C.centeredAt x hx).spine =
      neighborsIn G x C.vertexFinset := by
  classical
  have hxSupport : x ∈ C.walk.support := by
    simpa [CycleWitness.vertexFinset] using hx
  let r : G.Walk x x := C.walk.rotate x hxSupport
  have hr : r.IsCycle := C.isCycle.rotate hxSupport
  have htailNotNil : ¬ r.tail.Nil := by
    intro hnil
    have htailLength : r.tail.length + 1 = r.length :=
      r.length_tail_add_one hr.not_nil
    have hzero : r.tail.length = 0 := hnil.length_eq_zero
    have hthree : 3 ≤ r.length := hr.three_le_length
    omega
  have hfullSupport :
      r.support = x :: (r.tail.dropLast.support ++ [x]) := by
    calc
      r.support = x :: r.tail.support :=
        (r.cons_support_tail hr.not_nil).symm
      _ = x :: (r.tail.dropLast.support ++ [x]) := by
        rw [r.tail.support_dropLast_concat htailNotNil]
  ext y
  simp only [walkNeighbors, neighborsIn, Finset.mem_filter,
    List.mem_toFinset, CycleWitness.vertexFinset]
  constructor
  · rintro ⟨hySpine, hxy⟩
    change y ∈ r.tail.dropLast.support at hySpine
    refine ⟨?_, hxy⟩
    have hyr : y ∈ r.support := by
      rw [hfullSupport]
      simp [hySpine]
    exact (C.walk.mem_support_rotate_iff x hxSupport).mp hyr
  · rintro ⟨hyCycle, hxy⟩
    refine ⟨?_, hxy⟩
    have hyr : y ∈ r.support :=
      (C.walk.mem_support_rotate_iff x hxSupport).mpr hyCycle
    rw [hfullSupport] at hyr
    simp only [List.mem_cons, List.mem_append] at hyr
    rcases hyr with hyx | hySpine | hyx
    · exact (hxy.ne hyx.symm).elim
    · change y ∈ r.tail.dropLast.support
      exact hySpine
    · rcases hyx with hyx | hyfalse
      · exact (hxy.ne hyx.symm).elim
      · exact (List.not_mem_nil hyfalse).elim

/-- Manuscript Lemma `lem:cycle-degree` in its literal arbitrary-cycle
form: every vertex has induced-cycle degree at most `k+1`. -/
theorem cycle_degree_on_cycle
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G) (x : V) (hx : x ∈ C.vertexFinset) :
    (G.induce (↑C.vertexFinset : Set V)).degree ⟨x, hx⟩ ≤ k + 1 := by
  classical
  have hcentered := cycle_degree hfree (C.centeredAt x hx)
  change (walkNeighbors x (C.centeredAt x hx).spine).card ≤ k + 1 at hcentered
  rw [C.walkNeighbors_centeredAt x hx] at hcentered
  calc
    (G.induce (↑C.vertexFinset : Set V)).degree ⟨x, hx⟩ =
        ((G.induce (↑C.vertexFinset : Set V)).neighborFinset ⟨x, hx⟩).card := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ = (((G.induce (↑C.vertexFinset : Set V)).neighborFinset ⟨x, hx⟩).map
        (Function.Embedding.subtype (· ∈ (↑C.vertexFinset : Set V)))).card := by
          rw [Finset.card_map]
    _ = (G.neighborFinset x ∩ C.vertexFinset).card := by
      congr 1
      ext y
      simp
    _ = (neighborsIn G x C.vertexFinset).card := by
      congr 1
      ext y
      simp [neighborsIn, and_comm]
    _ ≤ k + 1 := hcentered

/-- The maximum in the definition of `p k n` is attained because `A k` is
nonempty and finite. -/
theorem exists_maximizing_splitTerm (k n : ℕ) :
    ∃ a, a ∈ A k ∧ p k n = splitTerm k n a := by
  simpa [p] using
    (Finset.exists_mem_eq_sup (A k) ⟨k + 1, top_mem_A k⟩ (splitTerm k n))

theorem splitTerm_shift {k m n a : ℕ} (ham : a ≤ m) (hmn : m ≤ n) :
    splitTerm k n a = splitTerm k m a + (n - m) * a := by
  have hsub : n - a = (m - a) + (n - m) := by omega
  unfold splitTerm
  rw [hsub, Nat.mul_add]
  ac_rfl

theorem t_shift_le_of_two_mul_le {k m n a : ℕ} (hmn : m ≤ n)
    (ha : k + 1 ≤ 2 * a) :
    t k n ≤ t k m + (n - m) * a := by
  let d := n - m
  have hn : n = m + d := by omega
  have hdivadd : ((k + 1) * m + (k + 1) * d) / 2 ≤
      ((k + 1) * m) / 2 + ((k + 1) * d + 1) / 2 := by omega
  have hpart : ((k + 1) * d + 1) / 2 ≤ d * a := by
    have hpoly : (k + 1) * d ≤ 2 * (d * a) := by
      nlinarith
    omega
  have hcore : ((k + 1) * m + (k + 1) * d) / 2 ≤
      ((k + 1) * m) / 2 + d * a :=
    hdivadd.trans (Nat.add_le_add_left hpart _)
  unfold t
  calc
    ((k + 1) * n) / 2 = ((k + 1) * m + (k + 1) * d) / 2 := by
      rw [hn, Nat.mul_add]
    _ ≤ ((k + 1) * m) / 2 + d * a := hcore
    _ = ((k + 1) * m) / 2 + (n - m) * a := by rfl

/-- Claim `claim:Sk-linear-increment` (ii): once the `t` branch is maximal,
every earlier order in the base range is also on the `t` branch.  Part (i)
is `p_succ_ge_of_eq_splitTerm` in `Arithmetic.lean`. -/
theorem h_eq_t_descends {k m n : ℕ} (_hk : 2 ≤ k)
    (hm : k + 2 ≤ m) (hmn : m ≤ n) (hn : h k n = t k n) :
    h k m = t k m := by
  have hn0 : k + 2 ≤ n := hm.trans hmn
  have hpn : p k n ≤ t k n := by
    have hmax := h_eq_max hn0
    rw [hn] at hmax
    exact (le_max_right (t k n) (p k n)).trans_eq hmax.symm
  obtain ⟨a, haA, hpa⟩ := exists_maximizing_splitTerm k m
  have haBounds := mem_A_iff.mp haA
  have ham : a ≤ m := haBounds.2.trans (by omega)
  have hshift := splitTerm_shift (k := k) ham hmn
  have hpLower : p k m + (n - m) * a ≤ p k n := by
    rw [hpa, ← hshift]
    exact p_ge_splitTerm haA
  have htShift :=
    t_shift_le_of_two_mul_le (k := k) hmn (by omega : k + 1 ≤ 2 * a)
  have hpm : p k m ≤ t k m := by omega
  rw [h_eq_max hm, max_eq_left hpm]

/-- Mapping a path along a graph embedding maps its path-neighbor finset
bijectively. -/
theorem walkNeighbors_map_embedding
    {U : Type u} {W : Type w} [DecidableEq U] [DecidableEq W]
    {H : SimpleGraph U} {K : SimpleGraph W}
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    (f : H ↪g K) {x a b : U} (pth : H.Walk a b) :
    walkNeighbors (f x) (pth.map f.toHom) =
      (walkNeighbors x pth).map f.toEmbedding := by
  classical
  ext z
  constructor
  · intro hz
    have hzSupport : z ∈ (pth.map f.toHom).support := by
      simpa using (Finset.mem_filter.mp hz).1
    rw [SimpleGraph.Walk.support_map] at hzSupport
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hzSupport
    apply Finset.mem_map.mpr
    refine ⟨y, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simpa using hy, ?_⟩
    exact f.map_rel_iff.mp (Finset.mem_filter.mp hz).2
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨?_, f.map_rel_iff.mpr (Finset.mem_filter.mp hy).2⟩
    rw [SimpleGraph.Walk.support_map]
    simpa using (Finset.mem_filter.mp hy).1

/-- Path-fans are preserved by graph embeddings. -/
theorem HasPathFan.map_embedding
    {U : Type u} {W : Type w} [DecidableEq U] [DecidableEq W]
    {H : SimpleGraph U} {K : SimpleGraph W}
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    (f : H ↪g K) {ell : ℕ} (hfan : HasPathFan H ell) : HasPathFan K ell := by
  rcases hfan with ⟨x, a, b, pth, hp, hx, hcount⟩
  refine ⟨f x, f a, f b, pth.map f.toHom, hp.map f.injective, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map]
    simpa using hx
  · rw [walkNeighbors_map_embedding, Finset.card_map]
    exact hcount

/-- An induced subgraph of a path-fan-free graph is path-fan-free. -/
theorem pathFanFree_induce
    {U : Type u} [DecidableEq U] {H : SimpleGraph U} [DecidableRel H.Adj]
    (s : Set U) {ell : ℕ} (hfree : PathFanFree H ell) :
    PathFanFree (H.induce s) ell := by
  classical
  intro hfan
  exact hfree
    (HasPathFan.map_embedding (SimpleGraph.Embedding.induce (G := H) s) hfan)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The endpoint of a longest path has degree below `ell` in a
`PF_ell`-free graph.  This is the graph-theoretic engine of
`lem:terminal`. -/
theorem exists_low_degree_of_pathFanFree [Nonempty V] {ell : ℕ}
    (hell : 1 ≤ ell) (hfree : PathFanFree G ell) :
    ∃ x : V, G.degree x < ell := by
  obtain ⟨u, v, pth, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hsupport : ∀ w : V, G.Adj u w → w ∈ pth.support := by
    intro w huw
    by_contra hw
    have hext : (pth.cons huw.symm).IsPath := by
      simpa using And.intro hp hw
    have hle := hmax w v (pth.cons huw.symm) hext
    simp at hle
  by_contra hlow
  push Not at hlow
  have hellpos : 0 < ell := hell
  have hdegpos : 0 < G.degree u := lt_of_lt_of_le hellpos (hlow u)
  have hneighpos : 0 < (G.neighborFinset u).card := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hneighpos
  have huw : G.Adj u w := (G.mem_neighborFinset u w).mp hw
  have hp_not_nil : ¬ pth.Nil := by
    intro hnil
    have hs : pth.support = [u] := SimpleGraph.Walk.nil_iff_support_eq.mp hnil
    have hwu : w = u := by
      have := hsupport w huw
      rw [hs] at this
      simpa using this
    subst w
    exact huw.ne rfl
  have hsupport_eq : pth.support = u :: pth.tail.support :=
    (pth.cons_support_tail hp_not_nil).symm
  have hu_tail : u ∉ pth.tail.support := by
    have hnodup := hp.support_nodup
    rw [hsupport_eq] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hneighbor_tail : ∀ w : V, G.Adj u w → w ∈ pth.tail.support := by
    intro z huz
    have hz := hsupport z huz
    rw [hsupport_eq] at hz
    simp only [List.mem_cons] at hz
    exact hz.resolve_left huz.ne.symm
  have heq : walkNeighbors u pth.tail = G.neighborFinset u := by
    ext z
    rw [G.mem_neighborFinset]
    constructor
    · intro hz
      exact (Finset.mem_filter.mp hz).2
    · intro huz
      exact Finset.mem_filter.mpr ⟨by simpa using hneighbor_tail z huz, huz⟩
  apply hfree
  refine ⟨u, _, _, pth.tail, hp.tail, hu_tail, ?_⟩
  rw [heq, SimpleGraph.card_neighborFinset_eq_degree]
  exact hlow u

/-- Exact edge accounting after deleting a vertex. -/
theorem card_edgeFinset_eq_induce_compl_singleton_add_degree
    (x : V) :
    G.edgeFinset.card = (G.induce ({x} : Set V)ᶜ).edgeFinset.card + G.degree x := by
  have hdeg : G.degree x ≤ G.edgeFinset.card := by
    rw [← SimpleGraph.card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (G.incidenceFinset_subset x)
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  omega

/-- Every graph of order `n` avoiding `PF_ell` has at most `B` edges.
Quantification over the vertex type makes deletion usable without a hidden
reindexing assumption. -/
def UniversalEdgeBound (ell n B : ℕ) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj],
    Fintype.card U = n → PathFanFree H ell → H.edgeFinset.card ≤ B

/-- The complete longest-path endpoint induction in `lem:terminal`. -/
theorem terminal_bound_of_base {k n₀ : ℕ} (hn₀ : k + 2 ≤ n₀)
    (hbase : UniversalEdgeBound.{u} (k + 2) n₀ ((k + 1) * (n₀ - k - 1)))
    {n : ℕ} (hn : n₀ ≤ n) :
    UniversalEdgeBound.{u} (k + 2) n ((k + 1) * (n - k - 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro U instU instDec H instAdj hcard hfree
      by_cases hEq : n = n₀
      · simpa [hEq] using hbase U H (hcard.trans hEq) hfree
      · have hnlt : n₀ < n := lt_of_le_of_ne hn (Ne.symm hEq)
        have hcardpos : 0 < Fintype.card U := by omega
        letI : Nonempty U := Fintype.card_pos_iff.mp hcardpos
        obtain ⟨x, hx⟩ :=
          exists_low_degree_of_pathFanFree (G := H) (ell := k + 2) (by omega) hfree
        have hxle : H.degree x ≤ k + 1 := by omega
        let s : Set U := ({x} : Set U)ᶜ
        have hcardS : Fintype.card s = n - 1 := by
          dsimp [s]
          rw [Fintype.card_compl_set ({x} : Set U)]
          simp [hcard]
        have hnPrev : n₀ ≤ n - 1 := by omega
        have hprev := ih (n - 1) (by omega) hnPrev
        have hfreeS : PathFanFree (H.induce s) (k + 2) :=
          pathFanFree_induce s hfree
        have hedgeS : (H.induce s).edgeFinset.card ≤
            (k + 1) * ((n - 1) - k - 1) :=
          hprev s (H.induce s) hcardS hfreeS
        have hedgeEq : H.edgeFinset.card =
            (H.induce s).edgeFinset.card + H.degree x := by
          simpa [s] using
            (card_edgeFinset_eq_induce_compl_singleton_add_degree (G := H) x)
        have hsub : ((n - 1) - k - 1) + 1 = n - k - 1 := by
          omega
        calc
          H.edgeFinset.card = (H.induce s).edgeFinset.card + H.degree x := hedgeEq
          _ ≤ (k + 1) * ((n - 1) - k - 1) + H.degree x :=
            Nat.add_le_add_right hedgeS _
          _ ≤ (k + 1) * ((n - 1) - k - 1) + (k + 1) :=
            Nat.add_le_add_left hxle _
          _ = (k + 1) * (((n - 1) - k - 1) + 1) := by
            rw [Nat.mul_succ]
          _ = (k + 1) * (n - k - 1) := by rw [hsub]

/-- Manuscript Lemma `lem:terminal`, with `lem:base` exposed as the premise
from which the paper derives its base case. -/
theorem terminal_bound
    {k n : ℕ} (hk : 2 ≤ k) (hn : (5 * k + 2) / 2 ≤ n)
    (hbase : UniversalEdgeBound.{u} (k + 2) ((5 * k + 2) / 2)
      (h k ((5 * k + 2) / 2))) :
    UniversalEdgeBound.{u} (k + 2) n ((k + 1) * (n - k - 1)) := by
  let n₀ := (5 * k + 2) / 2
  have hn₀ : k + 2 ≤ n₀ := by
    dsimp [n₀]
    omega
  have hformula : h k n₀ = (k + 1) * (n₀ - k - 1) := by
    apply h_eq_terminal hk
    exact le_rfl
  have hbase' : UniversalEdgeBound.{u} (k + 2) n₀
      ((k + 1) * (n₀ - k - 1)) := by
    have hbase₀ : UniversalEdgeBound.{u} (k + 2) n₀ (h k n₀) := by
      simpa [n₀] using hbase
    rw [hformula] at hbase₀
    exact hbase₀
  exact terminal_bound_of_base hn₀ hbase' (by simpa [n₀] using hn)

end Erdos767
