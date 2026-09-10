import Erdos767.BaseArithmetic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Binary vertex separations

This file supplies the finite graph decomposition used in the minimal
counterexample proof.  A graph of order at least four which is not
2-connected is covered by two proper induced subgraphs meeting in exactly
one vertex, with no edge crossing between their disjoint parts.
-/

open scoped Sym2

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

/-- A two-piece separation with one common cut vertex. -/
structure BinaryCutSeparation {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  X : Finset V
  Y : Finset V
  X_nonempty : X.Nonempty
  Y_nonempty : Y.Nonempty
  X_proper : X.card < Fintype.card V
  Y_proper : Y.card < Fintype.card V
  cover : X ∪ Y = Finset.univ
  overlap : (X ∩ Y).card = 1
  no_cross : ∀ ⦃x y : V⦄, x ∈ X \ Y → y ∈ Y \ X → ¬ G.Adj x y

namespace BinaryCutSeparation

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem card_add_sub_one (P : BinaryCutSeparation G) :
    P.X.card + P.Y.card - 1 = Fintype.card V := by
  have hcardUnion := Finset.card_union_add_card_inter P.X P.Y
  rw [P.cover, Finset.card_univ, P.overlap] at hcardUnion
  omega

/-- Every edge belongs to at least one of the two induced pieces. -/
theorem edgeFinset_card_le_induced_add (P : BinaryCutSeparation G) :
    G.edgeFinset.card ≤
      (G.induce (↑P.X : Set V)).edgeFinset.card +
        (G.induce (↑P.Y : Set V)).edgeFinset.card := by
  classical
  let EX := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ P.X
  let EY := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ P.Y
  have hcoverEdges : G.edgeFinset ⊆ EX ∪ EY := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he
      by_cases haX : a ∈ P.X
      · by_cases hbX : b ∈ P.X
        · apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨he, ?_⟩
          simpa [Finset.subset_iff] using And.intro haX hbX
        · have hbY : b ∈ P.Y := by
            have : b ∈ P.X ∪ P.Y := by rw [P.cover]; simp
            simpa [hbX] using this
          have haY : a ∈ P.Y := by
            by_contra haY
            have haDiff : a ∈ P.X \ P.Y :=
              Finset.mem_sdiff.mpr ⟨haX, haY⟩
            have hbDiff : b ∈ P.Y \ P.X :=
              Finset.mem_sdiff.mpr ⟨hbY, hbX⟩
            exact P.no_cross haDiff hbDiff hab
          apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨he, ?_⟩
          simpa [Finset.subset_iff, haY, hbY]
      · have haY : a ∈ P.Y := by
          have : a ∈ P.X ∪ P.Y := by rw [P.cover]; simp
          simpa [haX] using this
        have hbY : b ∈ P.Y := by
          by_contra hbY
          have hbX : b ∈ P.X := by
            have : b ∈ P.X ∪ P.Y := by rw [P.cover]; simp
            simpa [hbY] using this
          have hbDiff : b ∈ P.X \ P.Y :=
            Finset.mem_sdiff.mpr ⟨hbX, hbY⟩
          have haDiff : a ∈ P.Y \ P.X :=
            Finset.mem_sdiff.mpr ⟨haY, haX⟩
          exact P.no_cross hbDiff haDiff hab.symm
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨he, ?_⟩
        simpa [Finset.subset_iff, haY, hbY]
  have hcard := Finset.card_le_card hcoverEdges
  have hunion := Finset.card_union_le EX EY
  have hEX : EX.card =
      (G.induce (↑P.X : Set V)).edgeFinset.card := by
    simpa [EX] using G.card_filter_edgeFinset_toFinset_subset P.X
  have hEY : EY.card =
      (G.induce (↑P.Y : Set V)).edgeFinset.card := by
    simpa [EY] using G.card_filter_edgeFinset_toFinset_subset P.Y
  rw [hEX, hEY] at hunion
  exact hcard.trans hunion

end BinaryCutSeparation

/-- A graph of order at least four which is not 2-connected has a binary
cut separation.  The construction takes a connected component after deleting
a suitable vertex. -/
theorem exists_binaryCutSeparation_of_not_twoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsTwoConnected G) :
    Nonempty (BinaryCutSeparation G) := by
  classical
  have hthree : 3 ≤ Fintype.card V := by omega
  have hnotAll : ¬ ∀ z : V, (G.induce ({z} : Set V)ᶜ).Connected := by
    intro hall
    exact hnot ⟨hthree, hall⟩
  push_neg at hnotAll
  obtain ⟨z, hzDisconnected⟩ := hnotAll
  let H := G.induce ({z} : Set V)ᶜ
  have hcardH : Fintype.card {x // x ∈ ({z} : Set V)ᶜ} =
      Fintype.card V - 1 := by simp
  letI : Nonempty {x // x ∈ ({z} : Set V)ᶜ} :=
    Fintype.card_pos_iff.mp (by rw [hcardH]; omega)
  have hnotPre : ¬ H.Preconnected := by
    intro hp
    exact hzDisconnected ⟨hp⟩
  simp only [SimpleGraph.Preconnected] at hnotPre
  push_neg at hnotPre
  obtain ⟨u, v, huv⟩ := hnotPre
  let c := H.connectedComponentMk u
  let A0 : Finset {x // x ∈ ({z} : Set V)ᶜ} := c.supp.toFinset
  let emb : {x // x ∈ ({z} : Set V)ᶜ} ↪ V :=
    Function.Embedding.subtype _
  let A : Finset V := A0.map emb
  let X : Finset V := A ∪ {z}
  let Y : Finset V := Finset.univ \ A
  have huA0 : u ∈ A0 := by
    simp [A0, c, ConnectedComponent.connectedComponentMk_mem]
  have huA : (u : V) ∈ A := by
    exact Finset.mem_map.mpr ⟨u, huA0, rfl⟩
  have hzNotA : z ∉ A := by
    intro hzA
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp hzA
    have hwne : (w : V) ≠ z := by
      intro heq
      have hwNot : (w : V) ∉ ({z} : Set V) := w.property
      exact hwNot (by simp [heq])
    exact hwne hwz
  have hvNotA : (v : V) ∉ A := by
    intro hvA
    obtain ⟨w, hwA0, hwv⟩ := Finset.mem_map.mp hvA
    have hwComp : (w : _) ∈ c.supp := by simpa [A0] using hwA0
    have hwEq : w = v := by
      apply Subtype.ext
      exact hwv
    subst w
    have hvReach : H.Reachable v u := by
      exact ConnectedComponent.reachable_of_mem_supp c hwComp
        ConnectedComponent.connectedComponentMk_mem
    exact huv hvReach.symm
  have hvNeZ : (v : V) ≠ z := by
    intro heq
    have hvNot : (v : V) ∉ ({z} : Set V) := v.property
    exact hvNot (by simp [heq])
  have hXnonempty : X.Nonempty := ⟨z, by simp [X]⟩
  have hYnonempty : Y.Nonempty := ⟨(v : V), by simp [Y, hvNotA]⟩
  have hXproper : X.card < Fintype.card V := by
    apply Finset.card_lt_card
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hrev
    have hvX : (v : V) ∈ X := hrev (Finset.mem_univ _)
    simp only [X, Finset.mem_union, Finset.mem_singleton] at hvX
    exact hvX.elim hvNotA (fun hvz => hvNeZ hvz)
  have hYproper : Y.card < Fintype.card V := by
    apply Finset.card_lt_card
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hrev
    have huY : (u : V) ∈ Y := hrev (Finset.mem_univ _)
    exact (Finset.mem_sdiff.mp huY).2 huA
  have hcover : X ∪ Y = Finset.univ := by
    ext x
    simp [X, Y]
  have hoverlap : (X ∩ Y).card = 1 := by
    have hXY : X ∩ Y = {z} := by
      ext x
      simp only [X, Y, Finset.mem_inter, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxA | hxz, hxNotA⟩
        · exact (hxNotA hxA).elim
        · exact hxz
      · intro hxz
        subst x
        exact ⟨Or.inr rfl, hzNotA⟩
    rw [hXY]
    simp
  have hnoCross : ∀ ⦃x y : V⦄,
      x ∈ X \ Y → y ∈ Y \ X → ¬ G.Adj x y := by
    intro x y hx hy hxy
    have hxX := (Finset.mem_sdiff.mp hx).1
    have hxNotY := (Finset.mem_sdiff.mp hx).2
    have hyY := (Finset.mem_sdiff.mp hy).1
    have hyNotX := (Finset.mem_sdiff.mp hy).2
    have hxA : x ∈ A := by
      rcases Finset.mem_union.mp hxX with hxA | hxz
      · exact hxA
      · have : x = z := by simpa using hxz
        subst x
        exact (hxNotY (by simp [Y, hzNotA])).elim
    have hyNotA : y ∉ A := (Finset.mem_sdiff.mp hyY).2
    have hyNeZ : y ≠ z := by
      intro hyz
      subst y
      exact hyNotX (by simp [X])
    obtain ⟨xx, hxxA0, hxx⟩ := Finset.mem_map.mp hxA
    let yy : {w // w ∈ ({z} : Set V)ᶜ} := ⟨y, by simpa using hyNeZ⟩
    have hAdjH : H.Adj xx yy := by
      change G.Adj (xx : V) (yy : V)
      have hxxVal : (xx : V) = x := by simpa [emb] using hxx
      simpa [yy, hxxVal] using hxy
    have hxxComp : xx ∈ c.supp := by simpa [A0] using hxxA0
    have hyyComp : yy ∈ c.supp :=
      (ConnectedComponent.mem_supp_congr_adj c hAdjH).mp hxxComp
    have hyyA0 : yy ∈ A0 := by simpa [A0] using hyyComp
    have hyA : y ∈ A := by
      apply Finset.mem_map.mpr
      exact ⟨yy, hyyA0, rfl⟩
    exact hyNotA hyA
  exact ⟨⟨X, Y, hXnonempty, hYnonempty, hXproper, hYproper,
    hcover, hoverlap, hnoCross⟩⟩

/-- Under the base-range induction hypothesis, every non-2-connected graph
already satisfies the desired edge bound. -/
theorem edge_bound_of_not_twoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2)
    (hcard : Fintype.card V = n) (hfree : PathFanFree G (k + 2))
    (hIH : ∀ m : ℕ, k + 2 ≤ m → m < n →
      UniversalEdgeBound.{u} (k + 2) m (h k m))
    (hnot : ¬ IsTwoConnected G) :
    G.edgeFinset.card ≤ h k n := by
  classical
  have hnFour : 4 ≤ n := by omega
  obtain ⟨P⟩ := exists_binaryCutSeparation_of_not_twoConnected G
    (by simpa [hcard] using hnFour) hnot
  let x := P.X.card
  let y := P.Y.card
  have hx0 : 1 ≤ x := Finset.card_pos.mpr P.X_nonempty
  have hy0 : 1 ≤ y := Finset.card_pos.mpr P.Y_nonempty
  have hxlt : x < n := by simpa [x, hcard] using P.X_proper
  have hylt : y < n := by simpa [y, hcard] using P.Y_proper
  have hxy : x + y - 1 = n := by
    simpa [x, y, hcard] using P.card_add_sub_one
  have pieceBound (S : Finset V) (hSlt : S.card < n) :
      (G.induce (↑S : Set V)).edgeFinset.card ≤ h k S.card := by
    by_cases hSsmall : S.card ≤ k + 1
    · have hedge := (G.induce (↑S : Set V)).card_edgeFinset_le_card_choose_two
      have hcardSubtype : Fintype.card {v // v ∈ (↑S : Set V)} = S.card := by
        simp
      rw [hcardSubtype] at hedge
      simpa [h, hSsmall] using hedge
    · have hSlarge : k + 2 ≤ S.card := by omega
      have hbound := hIH S.card hSlarge hSlt
      have hfreeS := pathFanFree_induce (↑S : Set V) hfree
      exact hbound {v // v ∈ (↑S : Set V)}
        (G.induce (↑S : Set V)) (by simp) hfreeS
  have hedgeX := pieceBound P.X hxlt
  have hedgeY := pieceBound P.Y hylt
  have hsplit := P.edgeFinset_card_le_induced_add
  have htoPieces : G.edgeFinset.card ≤ h k x + h k y := by
    exact hsplit.trans (Nat.add_le_add hedgeX hedgeY)
  by_cases hpt : p k n ≤ t k n
  · have hmerge := h_add_le_t_of_t_branch_cut hk hn hxy hx0 hy0
      hxlt hylt hpt
    exact htoPieces.trans (hmerge.trans (t_le_h hn))
  · have hcross : t k n < p k n := by omega
    have hmerge := merge_ineq_sub_one hk hn hnUpper hcross hx0 hy0
      (by omega : x + y - 1 ≤ n)
    rw [hxy] at hmerge
    exact htoPieces.trans hmerge

end

end Erdos767
