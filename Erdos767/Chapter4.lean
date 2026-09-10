import Erdos767.Chapter3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Chapter 4 foundations

This file gives kernel-checked definitions for the graph language introduced
at the beginning of Chapter 4: cycle witnesses, local maximality,
Hamiltonian-connectedness, 2-connectedness, and degree-sum closure.

The deep cited theorems in that chapter (Dirac, Ma--Ning,
Fan--Lv--Wang, and Erdős--Gallai) are deliberately not declared as axioms.
Their absence is therefore visible to downstream files rather than hidden
behind an unsound interface.
-/

open scoped Sym2

namespace Erdos767

open SimpleGraph

universe u

/-- A cycle together with its base vertex and its actual Mathlib walk. -/
structure CycleWitness {V : Type u} (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

namespace CycleWitness

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def length (C : CycleWitness G) : ℕ := C.walk.length

def vertexFinset (C : CycleWitness G) : Finset V := C.walk.support.toFinset

def edgeFinset (C : CycleWitness G) : Finset (Sym2 V) := C.walk.edges.toFinset

@[simp] theorem base_mem_vertexFinset (C : CycleWitness G) :
    C.base ∈ C.vertexFinset := by
  simp [vertexFinset]

end CycleWitness

section LocalMaximality

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Edges of `G` with one endpoint in `X` and the other in `Y`. -/
def edgesBetween (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦
    ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y)

/-- Edges of `D` crossing from the vertices of `C` to their complement. -/
def cycleCrossingEdges (C D : CycleWitness G) : Finset (Sym2 V) :=
  D.edgeFinset ∩ edgesBetween G C.vertexFinset (Finset.univ \ C.vertexFinset)

/-- The manuscript definition: no longer cycle may use at most two edges
between `V(C)` and its complement. -/
def IsLocallyMaximalCycle (C : CycleWitness G) : Prop :=
  ∀ D : CycleWitness G, C.length < D.length →
    3 ≤ (cycleCrossingEdges C D).card

def IsLongestCycle (C : CycleWitness G) : Prop :=
  ∀ D : CycleWitness G, D.length ≤ C.length

/-- The elementary assertion in the notation subsection that every longest
cycle is locally maximal. -/
theorem IsLongestCycle.isLocallyMaximal {C : CycleWitness G}
    (hC : IsLongestCycle C) : IsLocallyMaximalCycle C := by
  intro D hlong
  exact (not_lt_of_ge (hC D) hlong).elim

end LocalMaximality

section Connectivity

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every two distinct vertices are joined by a Hamilton path. -/
def IsHamiltonianConnected (G : SimpleGraph V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ p : G.Walk x y, p.IsHamiltonian

/-- Finite vertex-2-connectivity in the form used by the manuscript. -/
def IsTwoConnected (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧
    ∀ x : V, (G.induce ({x} : Set V)ᶜ).Connected

end Connectivity

section Closure

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- One simultaneous degree-sum closure step. -/
def closureStep (r : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.Adj x y ∨ r ≤ G.degree x + G.degree y)
  symm := ⟨by
    intro x y hxy
    refine ⟨hxy.1.symm, ?_⟩
    rcases hxy.2 with hxy | hdeg
    · exact Or.inl hxy.symm
    · exact Or.inr (by simpa [Nat.add_comm] using hdeg)⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩

instance closureStep_decidableAdj (r : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel (closureStep r G).Adj := by
  intro x y
  simp only [closureStep]
  infer_instance

@[simp] theorem closureStep_adj {r : ℕ} {G : SimpleGraph V}
    [DecidableRel G.Adj] {x y : V} :
    (closureStep r G).Adj x y ↔
      x ≠ y ∧ (G.Adj x y ∨ r ≤ G.degree x + G.degree y) := Iff.rfl

theorem le_closureStep (r : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    G ≤ closureStep r G := by
  intro x y hxy
  exact ⟨hxy.ne, Or.inl hxy⟩

/-- Degree-sum closedness at threshold `r`. -/
def IsRClosed (r : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ x y : V, x ≠ y → ¬ G.Adj x y → G.degree x + G.degree y < r

theorem closureStep_eq_self_iff (r : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    closureStep r G = G ↔ IsRClosed r G := by
  constructor
  · intro heq x y hxy hnon
    by_contra hdeg
    have hstep : (closureStep r G).Adj x y := ⟨hxy, Or.inr (by omega)⟩
    rw [heq] at hstep
    exact hnon hstep
  · intro hclosed
    ext x y
    constructor
    · rintro ⟨hxy, hadj | hdeg⟩
      · exact hadj
      · by_contra hnon
        exact (not_le_of_gt (hclosed x y hxy hnon)) hdeg
    · intro hxy
      exact ⟨hxy.ne, Or.inl hxy⟩

theorem card_edgeFinset_le_closureStep (r : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (closureStep r G).edgeFinset.card :=
  Finset.card_le_card (SimpleGraph.edgeFinset_mono (le_closureStep r G))

/-- The number of edges in the canonical `W_(n,s,t)` host from Chapter 4. -/
def wEdgeCount (n s t : ℕ) : ℕ :=
  (t - s + 1).choose 2 + s * (n - t + s - 1)

end Closure

end Erdos767
