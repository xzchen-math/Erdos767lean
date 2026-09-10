import Erdos767.Chapter4
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Explicit literature assumptions for Route A

This file states, but does not prove, the external graph-theoretic results
used in Chapters 4 and 5 of `ErdosProblem767.tex`.  They are collected in
the structure
`LiteratureTheorems`; downstream theorems must receive a value of that
structure as an explicit argument.

There are deliberately no global `axiom` declarations in this file.  Thus a
Route-A theorem has the logical form

`LiteratureTheorems -> statement proved in the paper`.

The auxiliary definitions below make the assumption boundary mathematical:
none of the fields is an unnamed placeholder proposition.
-/

open scoped Sym2

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

/-- Every finite graph relation is classically decidable.  This local
instance keeps the statement layer independent of how a downstream file
chooses to compute adjacency for graphs created by closure or switching. -/
local instance classicalDecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

section CommonDefinitions

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Two cycle witnesses in possibly different graphs describe the same
oriented cycle. -/
def SameCycle {G H : SimpleGraph V} (C : CycleWitness G)
    (D : CycleWitness H) : Prop :=
  C.base = D.base ∧ C.walk.support = D.walk.support ∧
    C.walk.edges = D.walk.edges

/-- A graph contains a cycle of length at least `m`. -/
def HasCycleLengthAtLeast (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ C : CycleWitness G, m ≤ C.length

/-- Repeated simultaneous degree-sum closure steps. -/
def closureIterate (r : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → SimpleGraph V
  | 0 => G
  | i + 1 => closureStep r (closureIterate r G i)

/-- The finite degree-sum closure.  There are at most `choose |V| 2`
possible edges, so this many simultaneous steps reaches the standard fixed
point closure.  The fixed-point proof is kept separate from this definition. -/
def rClosure (r : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph V :=
  closureIterate r G ((Fintype.card V).choose 2)

/-- The closed graph on the subtype of vertices of `C`. -/
def cycleCoreClosure {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) : SimpleGraph {x // x ∈ C.vertexFinset} :=
  rClosure (C.length + 1)
    (G.induce (↑C.vertexFinset : Set V))

/-- The manuscript's `C`-closure: replace the graph induced by `V(C)` by
its `(length C + 1)`-closure and leave every other adjacency unchanged. -/
def cycleClosure {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) : SimpleGraph V :=
  G ⊔
    (cycleCoreClosure C).map
        (Function.Embedding.subtype (· ∈ C.vertexFinset))

/-- Vertices of `S` adjacent to `x`. -/
def neighborsIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (S : Finset V) : Finset V :=
  S.filter (G.Adj x)

/-- Vertices outside `S` having a neighbor in `S`. -/
def externalNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  Finset.univ.filter fun x ↦ x ∉ S ∧ ∃ y ∈ S, G.Adj x y

/-- Vertices in `T` having a neighbor in `S`. -/
def setNeighborsIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) : Finset V :=
  T.filter fun x ↦ ∃ y ∈ S, G.Adj x y

/-- `Q` is a connected component of the graph outside `C`.  Connectedness
is stated in the induced graph, and the last conjunct is maximality inside
`V \ V(C)`. -/
def IsComponentOutsideCycle {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : CycleWitness G) (Q : Finset V) : Prop :=
  Q.Nonempty ∧
    Q ⊆ Finset.univ \ C.vertexFinset ∧
    (G.induce (↑Q : Set V)).Connected ∧
    ∀ x ∈ Q, ∀ y ∈ Finset.univ \ C.vertexFinset,
      G.Adj x y → y ∈ Q

end CommonDefinitions

section HostFamilies

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A labeled copy of the canonical host `W_(n,s,t)` from Chapter 4. -/
def IsWGraph (H : SimpleGraph V) (n s t : ℕ) : Prop :=
  Fintype.card V = n ∧
    1 ≤ s ∧ s ≤ (t + 1) / 2 ∧ t - s + 1 ≤ n ∧
    ∃ S T U : Finset V,
      Disjoint S T ∧ Disjoint S U ∧ Disjoint T U ∧
      S ∪ T ∪ U = Finset.univ ∧
      S.card = s ∧ T.card = t - 2 * s + 1 ∧
      U.card = n - t + s - 1 ∧
      ∀ x y : V,
        H.Adj x y ↔
          x ≠ y ∧
            ((x ∈ S ∪ T ∧ y ∈ S ∪ T) ∨
             (x ∈ U ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ U))

/-- The labeled `W` host carried by a fixed ordered partition. -/
def wGraphFromPartition (S T U : Finset V) : SimpleGraph V where
  Adj x y :=
    x ≠ y ∧
      ((x ∈ S ∪ T ∧ y ∈ S ∪ T) ∨
       (x ∈ U ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ U))
  symm := ⟨by
    rintro x y ⟨hxy, h⟩
    refine ⟨hxy.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩

@[simp] theorem wGraphFromPartition_adj {S T U : Finset V} {x y : V} :
    (wGraphFromPartition S T U).Adj x y ↔
      x ≠ y ∧
        ((x ∈ S ∪ T ∧ y ∈ S ∪ T) ∨
         (x ∈ U ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ U)) := Iff.rfl

/-- `G` is a spanning subgraph of a labeled copy of `W_(n,s,t)`. -/
def IsSubgraphOfW (G : SimpleGraph V) (n s t : ℕ) : Prop :=
  ∃ H : SimpleGraph V, IsWGraph H n s t ∧ G ≤ H

/-- Membership in the exceptional family `X_(n,c)`. -/
def IsXGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (n c : ℕ) : Prop :=
  Fintype.card V = n ∧ Odd c ∧
    ∃ A B X : Finset V,
      Disjoint A B ∧ Disjoint A X ∧ Disjoint B X ∧
      A ∪ B ∪ X = Finset.univ ∧
      A.card = c / 2 ∧
      G.IsClique (A : Set V) ∧ G.IsIndepSet (B : Set V) ∧
      G.IsIndepSet (X : Set V) ∧
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
      ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧
        ∀ x ∈ X, G.neighborFinset x = {a, b}

/-- Explicit star-component data for the nontrivial star forest in the
definition of `Y_(n,c)`. -/
structure StarForestWitness (G : SimpleGraph V) (Y : Finset V) where
  componentCount : ℕ
  two_le_componentCount : 2 ≤ componentCount
  part : Fin componentCount → Finset V
  center : Fin componentCount → V
  center_mem : ∀ i, center i ∈ part i
  component_nontrivial : ∀ i, 2 ≤ (part i).card
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (part i) (part j)
  covers : ∀ v, v ∈ Y ↔ ∃ i, v ∈ part i
  induced_adj : ∀ x ∈ Y, ∀ y ∈ Y,
    G.Adj x y ↔
      ∃ i, x ∈ part i ∧ y ∈ part i ∧
        ((x = center i ∧ y ≠ center i) ∨
         (y = center i ∧ x ≠ center i))

/-- Membership in the exceptional family `Y_(n,c)`. -/
def IsYGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (n c : ℕ) : Prop :=
  Fintype.card V = n ∧ Odd c ∧
    ∃ A B Y : Finset V,
      Disjoint A B ∧ Disjoint A Y ∧ Disjoint B Y ∧
      A ∪ B ∪ Y = Finset.univ ∧
      A.card = c / 2 ∧
      G.IsClique (A : Set V) ∧ G.IsIndepSet (B : Set V) ∧
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
      ∃ F : StarForestWitness G Y,
        ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧
          (∀ i, externalNeighbors G (F.part i) = {a, b}) ∧
          ∀ i, 3 ≤ (F.part i).card →
            ∃ z ∈ ({a, b} : Finset V),
              ∀ x ∈ (F.part i).erase (F.center i),
                G.degree x = 2 ∧ G.Adj x z

/-- A graph is a subgraph of one of the two exceptional hosts. -/
def IsSubgraphOfExceptionalHost (G : SimpleGraph V) [DecidableRel G.Adj]
    (n c : ℕ) : Prop :=
  ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
    G ≤ H ∧ (IsXGraph H n c ∨ IsYGraph H n c)

end HostFamilies

section AttachmentsAndSwitching

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `ys` is a cyclic rotation of `xs`. -/
def IsListRotation (xs ys : List V) : Prop :=
  ∃ as bs : List V, xs = as ++ bs ∧ ys = bs ++ as

/-- A duplicate-free list is a subset of the vertices of `C`, written in
their cyclic order. -/
def IsCyclicListing (C : CycleWitness G) (T : List V) : Prop :=
  T.Nodup ∧
    2 ≤ T.length ∧
    ∃ R : List V,
      IsListRotation C.walk.support.dropLast R ∧ T.Sublist R

/-- `y` immediately follows `x` in a cyclic list, including the last-to-first
pair. -/
def IsCyclicSuccessor (T : List V) (x y : V) : Prop :=
  (∃ as bs : List V, T = as ++ x :: y :: bs) ∨
    ∃ middle : List V, T = y :: middle ++ [x]

/-- The manuscript definition of a strong attachment, represented by its
cyclically ordered attachment list. -/
def IsStrongAttachment (C : CycleWitness G) (Q : Finset V)
    (T : List V) : Prop :=
  IsCyclicListing C T ∧
    ∀ x y, IsCyclicSuccessor T x y →
      ∃ u ∈ Q, ∃ v ∈ Q,
        G.Adj x u ∧ G.Adj y v ∧
          Disjoint ({x, u} : Finset V) ({y, v} : Finset V)

/-- An `(x,Q,y)`-path: its endpoints lie outside `Q` and every internal
vertex lies in `Q`. -/
def IsPathThrough (Q : Finset V) {x y : V} (p : G.Walk x y) : Prop :=
  p.IsPath ∧ x ∉ Q ∧ y ∉ Q ∧
    p.support.toFinset \ {x, y} ⊆ Q

/-- A longest `(x,Q,y)`-path. -/
def IsLongestPathThrough (Q : Finset V) {x y : V}
    (p : G.Walk x y) : Prop :=
  IsPathThrough Q p ∧
    ∀ q : G.Walk x y, IsPathThrough Q q → q.length ≤ p.length

/-- The set of edges from `x` to vertices of `A`. -/
def starEdges (x : V) (A : Finset V) : Finset (Sym2 V) :=
  A.image fun z ↦ s(x, z)

/-- Edge switching `G[y -> x; A]`: delete `yz` and add `xz` for `z ∈ A`. -/
def edgeSwitch (G : SimpleGraph V) (y x : V) (A : Finset V) :
    SimpleGraph V :=
  G.deleteEdges (↑(starEdges y A) : Set (Sym2 V)) ⊔
    SimpleGraph.fromEdgeSet (↑(starEdges x A) : Set (Sym2 V))

/-- Properties of the resulting graph asserted by the Fan--Lv--Wang
switching lemma. -/
def IsSwitchingOutcome (G : SimpleGraph V) (C : CycleWitness G)
    (G' : SimpleGraph V) [DecidableRel G'.Adj] : Prop :=
  IsTwoConnected G' ∧
    (∃ C' : CycleWitness G', SameCycle C C' ∧
      IsLocallyMaximalCycle C') ∧
    G'.induce (↑C.vertexFinset : Set V) =
      G.induce (↑C.vertexFinset : Set V) ∧
    G.edgeFinset.card ≤ G'.edgeFinset.card

/-- The two alternatives in Fan--Lv--Wang Lemma 2.4, including the
properties of the graph produced in alternative (ii). -/
def FanLvWangAlternative (G : SimpleGraph V) (C : CycleWitness G)
    (Q : Finset V) : Prop :=
  (∀ x ∈ setNeighborsIn G Q C.vertexFinset,
      neighborsIn G x Q = Q) ∨
  ∃ x ∈ setNeighborsIn G Q C.vertexFinset,
    ∃ y ∈ neighborsIn G x Q,
      ∃ A : Finset V,
        A.Nonempty ∧
        A ⊆ neighborsIn G y Q \ neighborsIn G x Q ∧
        let G₀ := edgeSwitch G y x A
        IsSwitchingOutcome G C G₀ ∨
          (¬ IsTwoConnected G₀ ∧
            ∃ x' ∈ setNeighborsIn G Q C.vertexFinset,
              x' ≠ x ∧
              IsSwitchingOutcome G C
                (G₀ ⊔ SimpleGraph.edge y x'))

end AttachmentsAndSwitching

/-! ## Exact propositions imported from the literature -/

/-- Dirac's circumference theorem (`thm:Dirac-cycle`). -/
def DiracCycleTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsTwoConnected G →
      HasCycleLengthAtLeast G
        (min (Fintype.card V) (2 * G.minDegree))

/-- Ma--Ning exterior stability (`thm:MN-exterior-stability`). -/
def MaNingExteriorStabilityTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G),
    IsTwoConnected G → IsLongestCycle C →
    10 ≤ C.length → C.length < Fintype.card V →
    (C.length / 2 - 1) * (Fintype.card V - C.length) <
      (G.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
        (edgesBetween G (Finset.univ \ C.vertexFinset)
          C.vertexFinset).card →
    IsSubgraphOfW G (Fintype.card V) (C.length / 2) C.length ∨
      (Odd C.length ∧
        IsSubgraphOfExceptionalHost G (Fintype.card V) C.length)

/-- Ma--Ning Lemma 2.7 (`lem:closure-preserves-local-maximality`). -/
def ClosurePreservesLocalMaximalityTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G),
    IsLocallyMaximalCycle C →
      ∃ C' : CycleWitness (cycleClosure C),
        SameCycle C C' ∧ IsLocallyMaximalCycle C'

/-- Ma--Ning Lemma 2.8 (`lem:Ma-Ning-non-ha`). -/
def MaNingNonHamiltonianConnectedTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G),
    IsTwoConnected G → IsLocallyMaximalCycle C →
    C.length < Fintype.card V →
      ¬ IsHamiltonianConnected (cycleCoreClosure C)

/-- Ma--Ning Lemma 2.10 (`lem:Ma-Ning-degree`). -/
def MaNingDegreeTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    ¬ IsHamiltonianConnected G → 2 ≤ G.minDegree →
      ∃ s : ℕ, 2 ≤ s ∧ s ≤ Fintype.card V / 2 ∧
        ∃ S : Finset V, s - 1 ≤ S.card ∧
          ∀ x ∈ S, G.degree x ≤ s

/-- Ma--Ning Lemma 2.5(i) (`lem:Ma-Ning-strong-attachment`). -/
def MaNingStrongAttachmentTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G) (Q : Finset V) (T : List V) (d : ℕ),
    IsTwoConnected G → IsLocallyMaximalCycle C →
    IsComponentOutsideCycle C Q → IsStrongAttachment C Q T →
    2 ≤ d →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ∀ p : G.Walk x y,
        IsLongestPathThrough Q p → d ≤ p.length) →
    ∀ K : Finset V,
      K ⊆ C.vertexFinset → G.IsClique (K : Set V) →
        K.card ≤ C.length - (d - 1) * (T.length - 1)

/-- Fan--Lv--Wang Lemma 2.4 (`lem:Fan-Lv-Wang-switch`). -/
def FanLvWangSwitchTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G) (Q : Finset V),
    IsTwoConnected G → IsLocallyMaximalCycle C →
    IsComponentOutsideCycle C Q →
      FanLvWangAlternative G C Q

/-- Erdős--Gallai's path theorem (`lem:EG-path`). -/
def ErdosGallaiPathTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ell : ℕ),
    (∀ x y : V, ∀ p : G.Walk x y, p.IsPath → p.length ≤ ell) →
      G.edgeFinset.card ≤ ell * Fintype.card V / 2

/-- Theorem `thm:Posa-chorded-cycle`, used for the `k = 1` case of
`thm:main`: an
`n`-vertex graph with no singly chorded cycle (equivalently, no `PF_3`)
has at most `2n - 4` edges when `n ≥ 4`. -/
def PosaChordedCycleTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    4 ≤ Fintype.card V → PathFanFree G 3 →
      G.edgeFinset.card ≤ 2 * Fintype.card V - 4

/-- The complete and explicit Route-A trust boundary.  A value of this
structure supplies exactly the external theorems cited by Chapters 4 and 5.
All paper-specific deductions must be proved from such a value. -/
structure LiteratureTheorems where
  diracCycle : DiracCycleTheorem.{u}
  maNingExteriorStability : MaNingExteriorStabilityTheorem.{u}
  closurePreservesLocalMaximality :
    ClosurePreservesLocalMaximalityTheorem.{u}
  maNingNonHamiltonianConnected :
    MaNingNonHamiltonianConnectedTheorem.{u}
  maNingDegree : MaNingDegreeTheorem.{u}
  maNingStrongAttachment : MaNingStrongAttachmentTheorem.{u}
  fanLvWangSwitch : FanLvWangSwitchTheorem.{u}
  erdosGallaiPath : ErdosGallaiPathTheorem.{u}
  posaChordedCycle : PosaChordedCycleTheorem.{u}

end

end Erdos767
