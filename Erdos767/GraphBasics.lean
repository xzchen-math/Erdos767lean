import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Path-fans and cycles with incident chords

This file formalizes the basic graph-theoretic notions preceding
Lemma `lem:cycle-PF-equivalence` in `ErdosProblem767.tex`.

The ambient graph is a Mathlib `SimpleGraph`. Paths and cycles are Mathlib walks
satisfying `Walk.IsPath` and `Walk.IsCycle`; chords use Mathlib's
`Walk.IsChord`. A centered cycle stores the path left after deleting its
distinguished center. `CenteredCycle.walk_isCycle` proves that this
representation really produces a cycle in the ambient graph.
-/

open scoped Sym2

namespace Erdos767

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj]

def walkNeighbors {u v : V} (x : V) (p : G.Walk u v) : Finset V :=
  p.support.toFinset.filter (G.Adj x)

@[simp] theorem walkNeighbors_nil (x u : V) :
    walkNeighbors (G := G) x (.nil : G.Walk u u) =
      if G.Adj x u then {u} else ∅ := by
  classical
  unfold walkNeighbors
  change Finset.filter (G.Adj x) {u} = _
  rw [Finset.filter_singleton]

theorem exists_suffix_start_adj {x u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∉ p.support)
    (hneigh : 0 < (walkNeighbors x p).card) :
    ∃ (u' : V) (q : G.Walk u' v),
      q.IsPath ∧ x ∉ q.support ∧ G.Adj x u' ∧ walkNeighbors x q = walkNeighbors x p := by
  classical
  induction p with
  | @nil u =>
      by_cases hxu : G.Adj x u
      · refine ⟨u, .nil, .nil, hx, hxu, ?_⟩
        rfl
      · change 0 < (Finset.filter (G.Adj x) {u}).card at hneigh
        rw [Finset.filter_singleton] at hneigh
        simp [hxu] at hneigh
  | @cons u u' v hadj p ih =>
      by_cases hxu : G.Adj x u
      · exact ⟨u, .cons hadj p, hp, hx, hxu, rfl⟩
      · have hp' : p.IsPath := hp.of_cons
        have hx' : x ∉ p.support := by
          simp at hx
          exact hx.2
        have heq : walkNeighbors x p = walkNeighbors x (.cons hadj p) := by
          unfold walkNeighbors
          simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
          rw [Finset.filter_insert]
          simp [hxu]
        have hneigh' : 0 < (walkNeighbors x p).card := by
          rwa [heq]
        obtain ⟨u'', q, hq, hxq, hadjq, heqq⟩ := ih hp' hx' hneigh'
        exact ⟨u'', q, hq, hxq, hadjq, heqq.trans heq⟩

@[simp] theorem walkNeighbors_reverse {x u v : V} (p : G.Walk u v) :
    walkNeighbors x p.reverse = walkNeighbors x p := by
  unfold walkNeighbors
  simp

theorem exists_prefix_end_adj {x u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∉ p.support)
    (hneigh : 0 < (walkNeighbors x p).card) :
    ∃ (v' : V) (q : G.Walk u v'),
      q.IsPath ∧ x ∉ q.support ∧ G.Adj x v' ∧ walkNeighbors x q = walkNeighbors x p := by
  have hpR : p.reverse.IsPath := hp.reverse
  have hxR : x ∉ p.reverse.support := by simpa using hx
  have hnR : 0 < (walkNeighbors x p.reverse).card := by simpa using hneigh
  obtain ⟨v', q, hq, hxq, hadj, heq⟩ := exists_suffix_start_adj hpR hxR hnR
  refine ⟨v', q.reverse, hq.reverse, ?_, hadj, ?_⟩
  · simpa using hxq
  · simpa using heq

theorem exists_normalized_path {x u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∉ p.support)
    (hneigh : 0 < (walkNeighbors x p).card) :
    ∃ (u' v' : V) (q : G.Walk u' v'),
      q.IsPath ∧ x ∉ q.support ∧ G.Adj x u' ∧ G.Adj x v' ∧
        walkNeighbors x q = walkNeighbors x p := by
  obtain ⟨u', q, hq, hxq, hxu', heq⟩ := exists_suffix_start_adj hp hx hneigh
  have hnq : 0 < (walkNeighbors x q).card := by simpa [heq] using hneigh
  obtain ⟨v', r, hr, hxr, hxv', her⟩ := exists_prefix_end_adj hq hxq hnq
  exact ⟨u', v', r, hr, hxr, hxu', hxv', her.trans heq⟩

/-- Close a path `u P v` through a new center `x` to form `x u P v x`. -/
def closePath {x u v : V} (p : G.Walk u v)
    (hxu : G.Adj x u) (hvx : G.Adj v x) : G.Walk x x :=
  .cons hxu (p.concat hvx)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem closePath_isCycle {x u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∉ p.support) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    (closePath p hxu hxv.symm).IsCycle := by
  unfold closePath
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · exact hp.concat hx hxv.symm
  · simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton]
    rw [not_or]
    constructor
    · intro he
      exact hx (p.fst_mem_support_of_mem_edges he)
    · rw [Sym2.eq_iff]
      grind

/-- Vertices joined to `x` by chords of the closed walk `c`. -/
noncomputable def incidentChordVertices {u : V} (c : G.Walk u u) (x : V) : Finset V := by
  classical
  exact c.support.toFinset.filter fun w => c.IsChord s(x, w)

@[simp] theorem mem_incidentChordVertices {u x w : V} {c : G.Walk u u} :
    w ∈ incidentChordVertices c x ↔ c.IsChord s(x, w) := by
  classical
  simp [incidentChordVertices, SimpleGraph.Walk.isChord_sym2Mk]

theorem mem_incidentChordVertices_closePath_iff {x u v w : V} {p : G.Walk u v}
    (hx : x ∉ p.support)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    w ∈ incidentChordVertices (closePath p hxu hxv.symm) x ↔
      w ∈ walkNeighbors x p ∧ w ≠ u ∧ w ≠ v := by
  constructor
  · intro hw
    rw [mem_incidentChordVertices, SimpleGraph.Walk.isChord_sym2Mk] at hw
    rcases hw with ⟨hadj, hedge, -, hwmem⟩
    have hwp : w ∈ p.support := by
      simp [closePath] at hwmem
      rcases hwmem with rfl | hwp | rfl
      · exact (hadj.ne rfl).elim
      · exact hwp
      · exact (hadj.ne rfl).elim
    have hwu : w ≠ u := by
      intro h
      subst w
      apply hedge
      simp [closePath]
    have hwv : w ≠ v := by
      intro h
      subst w
      apply hedge
      simp [closePath]
    exact ⟨by simp [walkNeighbors, hwp, hadj], hwu, hwv⟩
  · rintro ⟨hw, hwu, hwv⟩
    have hwp : w ∈ p.support := by
      simpa using (Finset.mem_filter.mp hw).1
    have hadj : G.Adj x w := (Finset.mem_filter.mp hw).2
    rw [mem_incidentChordVertices, SimpleGraph.Walk.isChord_sym2Mk]
    refine ⟨hadj, ?_, by simp [closePath], by simp [closePath, hwp]⟩
    simp only [closePath, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    push Not
    refine ⟨?_, ?_, ?_⟩
    · intro he
      rw [Sym2.eq_iff] at he
      grind
    · intro he
      exact hx (p.fst_mem_support_of_mem_edges he)
    · intro he
      rw [Sym2.eq_iff] at he
      grind

theorem incidentChordVertices_closePath_eq {x u v : V} {p : G.Walk u v}
    (hx : x ∉ p.support)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    incidentChordVertices (closePath p hxu hxv.symm) x =
      ((walkNeighbors x p).erase u).erase v := by
  ext w
  rw [mem_incidentChordVertices_closePath_iff hx hxu hxv]
  simp only [Finset.mem_erase]
  tauto

/-- Number of chords of `c` incident with the distinguished vertex `x`. -/
noncomputable def incidentChordCount {u : V} (c : G.Walk u u) (x : V) : ℕ :=
  (incidentChordVertices c x).card

theorem incidentChordCount_closePath {x u v : V} {p : G.Walk u v}
    (hx : x ∉ p.support) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) :
    incidentChordCount (closePath p hxu hxv.symm) x =
      (walkNeighbors x p).card - 2 := by
  have hu : u ∈ walkNeighbors x p := by
    simp [walkNeighbors, hxu]
  have hv : v ∈ walkNeighbors x p := by
    simp [walkNeighbors, hxv]
  have hv' : v ∈ (walkNeighbors x p).erase u := by
    exact Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  rw [incidentChordCount, incidentChordVertices_closePath_eq hx hxu hxv,
    Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu]
  omega

theorem endpoints_ne_of_three_le_neighbors {x u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hthree : 3 ≤ (walkNeighbors x p).card) : u ≠ v := by
  intro huv
  subst v
  have hnil : p.Nil := SimpleGraph.Walk.isPath_iff_nil.mp hp
  have hp_eq : p = .nil := SimpleGraph.Walk.eq_nil_iff_nil.mpr hnil
  subst p
  change 3 ≤ (Finset.filter (G.Adj x) {u}).card at hthree
  rw [Finset.filter_singleton] at hthree
  split at hthree <;> simp_all

/-- The paper's path-fan predicate.  `x ∉ p.support` is exactly the condition
that the path lies in `G - x`. -/
def HasPathFan (G : SimpleGraph V) [DecidableRel G.Adj] (ell : ℕ) : Prop :=
  ∃ (x u v : V) (p : G.Walk u v),
    p.IsPath ∧ x ∉ p.support ∧ ell ≤ (walkNeighbors x p).card

/-- A cycle with a distinguished center, represented by the path left after
deleting that center. -/
structure CenteredCycle (G : SimpleGraph V) where
  center : V
  start : V
  finish : V
  spine : G.Walk start finish
  spine_isPath : spine.IsPath
  center_not_mem : center ∉ spine.support
  start_ne_finish : start ≠ finish
  adj_start : G.Adj center start
  adj_finish : G.Adj center finish

namespace CenteredCycle

/-- The actual closed walk `x u P v x` represented by a centered cycle. -/
def walk (C : CenteredCycle G) : G.Walk C.center C.center :=
  closePath C.spine C.adj_start C.adj_finish.symm

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem walk_isCycle (C : CenteredCycle G) : C.walk.IsCycle := by
  exact closePath_isCycle C.spine_isPath C.center_not_mem C.start_ne_finish
    C.adj_start C.adj_finish

noncomputable def chordCount (C : CenteredCycle G) : ℕ :=
  incidentChordCount C.walk C.center

theorem chordCount_eq (C : CenteredCycle G) :
    C.chordCount = (walkNeighbors C.center C.spine).card - 2 := by
  exact incidentChordCount_closePath C.center_not_mem C.start_ne_finish
    C.adj_start C.adj_finish

end CenteredCycle

/-- There is a cycle with a vertex incident with at least `k` chords. -/
def HasCycleWithIncidentChords (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ C : CenteredCycle G, k ≤ C.chordCount

/-- Lemma `lem:cycle-PF-equivalence` from `ErdosProblem767.tex`. -/
theorem cycle_pathFan_equivalence (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k) :
    HasPathFan G (k + 2) ↔ HasCycleWithIncidentChords G k := by
  constructor
  · rintro ⟨x, u, v, p, hp, hx, hcount⟩
    have hpos : 0 < (walkNeighbors x p).card := by omega
    obtain ⟨u', v', q, hq, hxq, hxu', hxv', heq⟩ :=
      exists_normalized_path hp hx hpos
    have hcount' : k + 2 ≤ (walkNeighbors x q).card := by simpa [heq] using hcount
    have hthree : 3 ≤ (walkNeighbors x q).card := by omega
    have huv : u' ≠ v' := endpoints_ne_of_three_le_neighbors hq hthree
    let C : CenteredCycle G :=
      { center := x
        start := u'
        finish := v'
        spine := q
        spine_isPath := hq
        center_not_mem := hxq
        start_ne_finish := huv
        adj_start := hxu'
        adj_finish := hxv' }
    refine ⟨C, ?_⟩
    rw [CenteredCycle.chordCount_eq]
    dsimp [C]
    omega
  · rintro ⟨C, hkC⟩
    refine ⟨C.center, C.start, C.finish, C.spine, C.spine_isPath,
      C.center_not_mem, ?_⟩
    rw [CenteredCycle.chordCount_eq] at hkC
    omega

end Erdos767
