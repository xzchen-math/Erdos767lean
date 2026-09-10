import Erdos767.Chapter4RouteA

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance switchDecidableGraph : DecidableEq (SimpleGraph V) :=
  Classical.decEq _
local instance (priority := 10) switchDecidableAdj (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _

def exteriorEdgeCount (C : CycleWitness G) (H : SimpleGraph V) : ℕ :=
  {e ∈ H.edgeFinset | e.toFinset ⊆ Finset.univ \ C.vertexFinset}.card

def SwitchingCandidate (H : SimpleGraph V) [DecidableRel H.Adj] (C : CycleWitness H)
    (K : SimpleGraph V) : Prop :=
  ∃ CK : CycleWitness K,
    SameCycle C CK ∧ IsTwoConnected K ∧ IsLocallyMaximalCycle CK ∧
      (∀ a ∈ C.vertexFinset, ∀ b ∈ C.vertexFinset,
        (K.Adj a b ↔ H.Adj a b)) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard

theorem edgeSet_ncard_eq_edgeFinset_card
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    K.edgeSet.ncard = K.edgeFinset.card := by
  symm
  exact K.edgeFinset_card.trans (Set.fintypeCard_eq_ncard K.edgeSet)

theorem SameCycle.refl (C : CycleWitness G) : SameCycle C C :=
  ⟨rfl, rfl, rfl⟩

theorem SameCycle.trans {H K : SimpleGraph V}
    {C : CycleWitness G} {D : CycleWitness H} {E : CycleWitness K}
    (hCD : SameCycle C D) (hDE : SameCycle D E) : SameCycle C E :=
  ⟨hCD.1.trans hDE.1, hCD.2.1.trans hDE.2.1,
    hCD.2.2.trans hDE.2.2⟩

def IsSwitchingTerminal (K : SimpleGraph V) (C : CycleWitness K) : Prop :=
  ∀ Q : Finset V, IsComponentOutsideCycle C Q →
    ∀ x, x ∈ C.vertexFinset → (∃ z ∈ Q, K.Adj x z) →
      ∀ y ∈ Q, K.Adj x y

theorem exists_min_switchingCandidate
    (H : SimpleGraph V) [hHAdj : DecidableRel H.Adj]
    (C : CycleWitness H) (h2c : IsTwoConnected H)
    (hloc : IsLocallyMaximalCycle C) :
    ∃ K : SimpleGraph V, SwitchingCandidate H C K ∧
      ∀ L : SimpleGraph V, SwitchingCandidate H C L →
        exteriorEdgeCount C K ≤ exteriorEdgeCount C L := by
  classical
  have hdec : hHAdj = switchDecidableAdj H := Subsingleton.elim _ _
  cases hdec
  let candidates := (Finset.univ : Finset (SimpleGraph V)).filter
    (SwitchingCandidate H C)
  have hHmem : H ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C, ⟨rfl, rfl, rfl⟩, h2c, hloc,
      (by intros; rfl), le_rfl⟩
  obtain ⟨K, hKmem, hmin⟩ := candidates.exists_min_image
    (fun K => exteriorEdgeCount C K) ⟨H, hHmem⟩
  refine ⟨K, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hKmem).2
  · intro L hL
    apply hmin
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩

theorem edgeSwitch_adj (K : SimpleGraph V) (y x : V) (A : Finset V)
    (a b : V) :
    (edgeSwitch K y x A).Adj a b ↔
      (K.Adj a b ∧ s(a, b) ∉ starEdges y A) ∨
        (s(a, b) ∈ starEdges x A ∧ a ≠ b) := by
  simp [edgeSwitch, starEdges]

theorem edgeSwitch_exterior_strict
    (K : SimpleGraph V) (C : CycleWitness K)
    (Q : Finset V) (hQ : IsComponentOutsideCycle C Q)
    (x : V) (hx : x ∈ setNeighborsIn K Q C.vertexFinset)
    (y : V) (hy : y ∈ neighborsIn K x Q)
    (A : Finset V) (hA : A.Nonempty)
    (hAsub : A ⊆ neighborsIn K y Q \ neighborsIn K x Q) :
    exteriorEdgeCount C (edgeSwitch K y x A) < exteriorEdgeCount C K := by
  classical
  let X := Finset.univ \ C.vertexFinset
  have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hx).1
  have hyQ : y ∈ Q := (Finset.mem_filter.mp hy).1
  have hyX : y ∈ X := hQ.2.1 hyQ
  obtain ⟨z, hzA⟩ := hA
  have hzSub := hAsub hzA
  have hzNY : z ∈ neighborsIn K y Q := (Finset.mem_sdiff.mp hzSub).1
  have hzNotNX : z ∉ neighborsIn K x Q := (Finset.mem_sdiff.mp hzSub).2
  have hzQ : z ∈ Q := (Finset.mem_filter.mp hzNY).1
  have hyzK : K.Adj y z := (Finset.mem_filter.mp hzNY).2
  have hzX : z ∈ X := hQ.2.1 hzQ
  have hxNotX : x ∉ X := by
    intro hxX
    exact (Finset.mem_sdiff.mp hxX).2 hxC
  have hle :
      (edgeSwitch K y x A).induce (↑X : Set V) ≤
        K.induce (↑X : Set V) := by
    intro a b hab
    change (edgeSwitch K y x A).Adj (a : V) (b : V) at hab
    rcases (edgeSwitch_adj K y x A (a : V) (b : V)).mp hab with
      hold | hnew
    · exact hold.1
    · rcases hnew with ⟨hstar, _⟩
      simp only [starEdges, Finset.mem_image] at hstar
      obtain ⟨w, hwA, hw⟩ := hstar
      rcases Sym2.eq_iff.mp hw with hw | hw
      · have hxa : x = (a : V) := hw.1
        exact (hxNotX (hxa ▸ a.property)).elim
      · have hxb : x = (b : V) := hw.1
        exact (hxNotX (hxb ▸ b.property)).elim
  let yy : ↥(↑X : Set V) := ⟨y, by simpa using hyX⟩
  let zz : ↥(↑X : Set V) := ⟨z, by simpa using hzX⟩
  have hyzBig : (K.induce (↑X : Set V)).Adj yy zz := hyzK
  have hyzSmall : ¬ ((edgeSwitch K y x A).induce
      (↑X : Set V)).Adj yy zz := by
    intro hsmall
    change (edgeSwitch K y x A).Adj y z at hsmall
    rcases (edgeSwitch_adj K y x A y z).mp hsmall with hold | hnew
    · exact hold.2 (Finset.mem_image.mpr ⟨z, hzA, rfl⟩)
    · rcases hnew with ⟨hstar, _⟩
      simp only [starEdges, Finset.mem_image] at hstar
      obtain ⟨w, hwA, hw⟩ := hstar
      rcases Sym2.eq_iff.mp hw with hw | hw
      · exact (hxNotX (hw.1 ▸ hyX)).elim
      · exact (hxNotX (hw.1 ▸ hzX)).elim
  have hstrict :
      (edgeSwitch K y x A).induce (↑X : Set V) <
        K.induce (↑X : Set V) := lt_of_le_of_ne hle (by
          intro heq
          apply hyzSmall
          rw [heq]
          exact hyzBig)
  unfold exteriorEdgeCount
  rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset,
    SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)

theorem edgeSwitch_add_cycle_edge_exterior_strict
    (K : SimpleGraph V) (C : CycleWitness K)
    (Q : Finset V) (hQ : IsComponentOutsideCycle C Q)
    (x : V) (hx : x ∈ setNeighborsIn K Q C.vertexFinset)
    (y : V) (hy : y ∈ neighborsIn K x Q)
    (A : Finset V) (hA : A.Nonempty)
    (hAsub : A ⊆ neighborsIn K y Q \ neighborsIn K x Q)
    (x' : V) (hx'C : x' ∈ C.vertexFinset) :
    exteriorEdgeCount C
        (edgeSwitch K y x A ⊔ SimpleGraph.edge y x') <
      exteriorEdgeCount C K := by
  classical
  let X := Finset.univ \ C.vertexFinset
  have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hx).1
  have hyQ : y ∈ Q := (Finset.mem_filter.mp hy).1
  have hyX : y ∈ X := hQ.2.1 hyQ
  obtain ⟨z, hzA⟩ := hA
  have hzSub := hAsub hzA
  have hzNY : z ∈ neighborsIn K y Q := (Finset.mem_sdiff.mp hzSub).1
  have hzQ : z ∈ Q := (Finset.mem_filter.mp hzNY).1
  have hyzK : K.Adj y z := (Finset.mem_filter.mp hzNY).2
  have hzX : z ∈ X := hQ.2.1 hzQ
  have hxNotX : x ∉ X := by
    intro hxX
    exact (Finset.mem_sdiff.mp hxX).2 hxC
  have hx'NotX : x' ∉ X := by
    intro hxX
    exact (Finset.mem_sdiff.mp hxX).2 hx'C
  let K' := edgeSwitch K y x A ⊔ SimpleGraph.edge y x'
  letI : DecidableRel K'.Adj := switchDecidableAdj K'
  have hle : K'.induce (↑X : Set V) ≤ K.induce (↑X : Set V) := by
    intro a b hab
    change K'.Adj (a : V) (b : V) at hab
    rcases hab with hswitch | hedge
    · rcases (edgeSwitch_adj K y x A (a : V) (b : V)).mp hswitch with
        hold | hnew
      · exact hold.1
      · rcases hnew with ⟨hstar, _⟩
        simp only [starEdges, Finset.mem_image] at hstar
        obtain ⟨w, hwA, hw⟩ := hstar
        rcases Sym2.eq_iff.mp hw with hw | hw
        · exact (hxNotX (hw.1 ▸ a.property)).elim
        · exact (hxNotX (hw.1 ▸ b.property)).elim
    · simp only [SimpleGraph.edge_adj] at hedge
      rcases hedge with ⟨hay, hbx'⟩ | ⟨hax', hby⟩
      · exact (hx'NotX (hbx' ▸ b.property)).elim
      · exact (hx'NotX (hax' ▸ a.property)).elim
  let yy : ↥(↑X : Set V) := ⟨y, by simpa using hyX⟩
  let zz : ↥(↑X : Set V) := ⟨z, by simpa using hzX⟩
  have hyzBig : (K.induce (↑X : Set V)).Adj yy zz := hyzK
  have hyzSmall : ¬ (K'.induce (↑X : Set V)).Adj yy zz := by
    intro hsmall
    change K'.Adj y z at hsmall
    rcases hsmall with hswitch | hedge
    · rcases (edgeSwitch_adj K y x A y z).mp hswitch with hold | hnew
      · exact hold.2 (Finset.mem_image.mpr ⟨z, hzA, rfl⟩)
      · rcases hnew with ⟨hstar, _⟩
        simp only [starEdges, Finset.mem_image] at hstar
        obtain ⟨w, hwA, hw⟩ := hstar
        rcases Sym2.eq_iff.mp hw with hw | hw
        · exact (hxNotX (hw.1 ▸ hyX)).elim
        · exact (hxNotX (hw.1 ▸ hzX)).elim
    · simp only [SimpleGraph.edge_adj] at hedge
      rcases hedge with ⟨_, hzx'⟩ | ⟨hyx', _⟩
      · exact (hx'NotX (hzx'.symm ▸ hzX)).elim
      · exact (hx'NotX (hyx'.symm ▸ hyX)).elim
  have hstrict : K'.induce (↑X : Set V) < K.induce (↑X : Set V) :=
    lt_of_le_of_ne hle (by
      intro heq
      apply hyzSmall
      rw [heq]
      exact hyzBig)
  unfold exteriorEdgeCount
  rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset,
    SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)

theorem exteriorEdgeCount_eq_of_sameCycle
    {H : SimpleGraph V} (C : CycleWitness G) (D : CycleWitness H)
    (hCD : SameCycle C D) (K : SimpleGraph V) :
    exteriorEdgeCount C K = exteriorEdgeCount D K := by
  have hv : C.vertexFinset = D.vertexFinset := by
    simp [CycleWitness.vertexFinset, hCD.2.1]
  unfold exteriorEdgeCount
  rw [hv]

theorem switching_terminal_structure_of_literature
    (lit : LiteratureTheorems.{u})
    (H : SimpleGraph V) [hHAdj : DecidableRel H.Adj]
    (C : CycleWitness H) (h2c : IsTwoConnected H)
    (hloc : IsLocallyMaximalCycle C) :
    ∃ (K : SimpleGraph V) (CK : CycleWitness K),
      SameCycle C CK ∧ IsTwoConnected K ∧ IsLocallyMaximalCycle CK ∧
      K.induce (↑C.vertexFinset : Set V) =
        H.induce (↑C.vertexFinset : Set V) ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      IsSwitchingTerminal K CK := by
  classical
  obtain ⟨K, hKcand, hmin⟩ :=
    exists_min_switchingCandidate H C h2c hloc
  rcases hKcand with ⟨CK, hSame, hK2c, hKloc, hCore, hEdgesN⟩
  have hEdges : H.edgeFinset.card ≤ K.edgeFinset.card := by
    rw [← edgeSet_ncard_eq_edgeFinset_card H,
      ← edgeSet_ncard_eq_edgeFinset_card K]
    exact hEdgesN
  have hInside : K.induce (↑C.vertexFinset : Set V) =
      H.induce (↑C.vertexFinset : Set V) := by
    ext a b
    exact hCore (a : V) a.property (b : V) b.property
  refine ⟨K, CK, hSame, hK2c, hKloc, hInside, hEdges, ?_⟩
  by_contra hNotTerminal
  apply hNotTerminal
  intro Q hQ xBad hxBadC hAttach yBad hyBad
  obtain ⟨zBad, hzBad, hxzBad⟩ := hAttach
  have hxBad : xBad ∈ setNeighborsIn K Q CK.vertexFinset :=
    Finset.mem_filter.mpr ⟨hxBadC, zBad, hzBad, hxzBad⟩
  have hAlt := lit.fanLvWangSwitch K CK Q hK2c hKloc hQ
  rcases hAlt with hComplete | hSwitch
  · have hyN : yBad ∈ neighborsIn K xBad Q := by
      rw [hComplete xBad hxBad]
      exact hyBad
    exact (Finset.mem_filter.mp hyN).2
  · rcases hSwitch with ⟨x, hx, y, hy, A, hA, hAsub, hOutcome⟩
    let G₀ := edgeSwitch K y x A
    rcases hOutcome with hOutcome₀ | hOutcomePlus
    · have hdec : inferInstanceAs (DecidableRel G₀.Adj) =
          switchDecidableAdj G₀ := Subsingleton.elim _ _
      cases hdec
      rcases hOutcome₀ with
        ⟨hG2c, ⟨CG, hCKCG, hGloc⟩, hGInside, hGEdges⟩
      have hCandG : SwitchingCandidate H C G₀ := by
        refine ⟨CG, hSame.trans hCKCG, hG2c, hGloc,
          ?_, ?_⟩
        intro a haC b hbC
        have hv : C.vertexFinset = CK.vertexFinset := by
          simp [CycleWitness.vertexFinset, hSame.2.1]
        have haCK : a ∈ CK.vertexFinset := by rwa [← hv]
        have hbCK : b ∈ CK.vertexFinset := by rwa [← hv]
        let aa : ↥(↑CK.vertexFinset : Set V) := ⟨a, haCK⟩
        let bb : ↥(↑CK.vertexFinset : Set V) := ⟨b, hbCK⟩
        have hAdjEq := congrArg (fun J : SimpleGraph
            (↥(↑CK.vertexFinset : Set V)) => J.Adj aa bb) hGInside
        have hGK : G₀.Adj a b ↔ K.Adj a b := by simpa [aa, bb] using hAdjEq
        exact hGK.trans (hCore a haC b hbC)
        apply hEdgesN.trans
        rw [edgeSet_ncard_eq_edgeFinset_card K,
          edgeSet_ncard_eq_edgeFinset_card G₀]
        exact hGEdges
      have hMinG := hmin G₀ hCandG
      have hStrictCK := edgeSwitch_exterior_strict
        K CK Q hQ x hx y hy A hA hAsub
      have hEqK : exteriorEdgeCount C K = exteriorEdgeCount CK K :=
        exteriorEdgeCount_eq_of_sameCycle C CK hSame K
      have hEqG : exteriorEdgeCount C G₀ = exteriorEdgeCount CK G₀ :=
        exteriorEdgeCount_eq_of_sameCycle C CK hSame G₀
      dsimp [G₀] at hMinG hEqG
      omega
    · rcases hOutcomePlus with
        ⟨hNot2c, x', hx', hx'ne, hOutcome'⟩
      let G' := G₀ ⊔ SimpleGraph.edge y x'
      rcases hOutcome' with
        ⟨hG2c, ⟨CG, hCKCG, hGloc⟩, hGInside, hGEdges⟩
      let d' : DecidableRel G'.Adj := inferInstance
      have hdec : d' = switchDecidableAdj G' := Subsingleton.elim _ _
      have hGlocGeneric : @IsLocallyMaximalCycle V _ _ G'
          (switchDecidableAdj G') CG := by
        rw [← hdec]
        exact hGloc
      have hCandG : SwitchingCandidate H C G' := by
        refine ⟨CG, hSame.trans hCKCG, hG2c, hGlocGeneric,
          ?_, ?_⟩
        intro a haC b hbC
        have hv : C.vertexFinset = CK.vertexFinset := by
          simp [CycleWitness.vertexFinset, hSame.2.1]
        have haCK : a ∈ CK.vertexFinset := by rwa [← hv]
        have hbCK : b ∈ CK.vertexFinset := by rwa [← hv]
        let aa : ↥(↑CK.vertexFinset : Set V) := ⟨a, haCK⟩
        let bb : ↥(↑CK.vertexFinset : Set V) := ⟨b, hbCK⟩
        have hAdjEq := congrArg (fun J : SimpleGraph
            (↥(↑CK.vertexFinset : Set V)) => J.Adj aa bb) hGInside
        have hGK : G'.Adj a b ↔ K.Adj a b := by
          simpa [G', aa, bb] using hAdjEq
        exact hGK.trans (hCore a haC b hbC)
        apply hEdgesN.trans
        rw [edgeSet_ncard_eq_edgeFinset_card K,
          edgeSet_ncard_eq_edgeFinset_card G']
        simpa [G', G₀] using hGEdges
      have hMinG := hmin G' hCandG
      have hx'C : x' ∈ CK.vertexFinset := (Finset.mem_filter.mp hx').1
      have hStrictCK := edgeSwitch_add_cycle_edge_exterior_strict
        K CK Q hQ x hx y hy A hA hAsub x' hx'C
      have hEqK : exteriorEdgeCount C K = exteriorEdgeCount CK K :=
        exteriorEdgeCount_eq_of_sameCycle C CK hSame K
      have hEqG : exteriorEdgeCount C G' = exteriorEdgeCount CK G' :=
        exteriorEdgeCount_eq_of_sameCycle C CK hSame G'
      dsimp [G', G₀] at hMinG hEqG
      omega

end

end Erdos767
