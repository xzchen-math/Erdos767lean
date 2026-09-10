import Erdos767.CycleSuccessors

namespace Erdos767
open SimpleGraph
universe u
noncomputable section
set_option maxHeartbeats 1000000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance cycleClosureDecidableAdj (C : CycleWitness G) :
    DecidableRel (cycleClosure C).Adj := Classical.decRel _

theorem cycleClosure_edgesBetween_outside_eq (C : CycleWitness G) :
    edgesBetween (cycleClosure C) (Finset.univ \ C.vertexFinset)
        C.vertexFinset =
      edgesBetween G (Finset.univ \ C.vertexFinset) C.vertexFinset := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heHC, x, hxOut, y, hyC, rfl⟩ :=
      Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨?_, x, hxOut, y, hyC, rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at heHC ⊢
    change G.Adj x y ∨
      ((cycleCoreClosure C).map
        (Function.Embedding.subtype (· ∈ C.vertexFinset))).Adj x y at heHC
    rcases heHC with hxy | hxy
    · exact hxy
    · obtain ⟨u, v, huv, hu, hv⟩ :=
        (SimpleGraph.map_adj _ _ _ _).mp hxy
      have hxNotC : x ∉ C.vertexFinset :=
        (Finset.mem_sdiff.mp hxOut).2
      exact (hxNotC (hu ▸ u.property)).elim
  · intro he
    obtain ⟨heG, x, hxOut, y, hyC, rfl⟩ := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨?_, x, hxOut, y, hyC, rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at heG ⊢
    exact (le_cycleClosure C) heG

/-- Positive-longest-path branch of Ma--Ning edge Lemma (i).  A clique of
order `c-s+1` on the cycle forces the selected terminal component to have
weight at most `2s`. -/
theorem terminal_component_weight_le_of_positive_and_clique
    (lit : LiteratureTheorems.{u})
    (C : CycleWitness G) (h2c : IsTwoConnected G)
    (hloc : IsLocallyMaximalCycle C)
    (hterminal : IsSwitchingTerminal G C)
    (c : (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (s : ℕ) (hs2 : 2 ≤ s) (hsc : s ≤ C.length)
    (hell : 1 ≤ componentLongestPathLength C c)
    (A : Finset V) (hAsub : A ⊆ C.vertexFinset)
    (hAcard : A.card = C.length - s + 1)
    (hAclique : G.IsClique (↑A : Set V)) :
    componentWeight C c ≤ 2 * s := by
  classical
  let T := componentAttachmentList C c
  have hq2 := two_le_componentAttachmentCount C h2c c
  have hTstrong : IsStrongAttachment C (componentOutsideFinset C c) T := by
    simpa [T] using componentAttachmentList_isStrong C h2c hterminal c hell
  have hTlen : T.length = componentAttachmentCount C c := by
    simpa [T] using length_componentAttachmentList C c
  have hpathLower : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ∀ p : G.Walk x y,
        IsLongestPathThrough (componentOutsideFinset C c) p →
          componentLongestPathLength C c + 2 ≤ p.length := by
    intro x hx y hy hxy p hp
    apply longest_path_through_component_lower C hterminal c x y
    · exact (mem_componentAttachmentList_iff C c x).mp (by simpa [T] using hx)
    · exact (mem_componentAttachmentList_iff C c y).mp (by simpa [T] using hy)
    · exact hxy
    · exact hp
  have hcliqueBound := lit.maNingStrongAttachment G C
    (componentOutsideFinset C c) T
    (componentLongestPathLength C c + 2)
    h2c hloc (componentOutsideFinset_isComponent C c)
    hTstrong (by omega) hpathLower A hAsub hAclique
  rw [hTlen] at hcliqueBound
  by_contra hweight
  have hlarge : 2 * s < componentWeight C c := by omega
  have hprod : s ≤ (componentLongestPathLength C c + 1) *
      (componentAttachmentCount C c - 1) := by
    unfold componentWeight at hlarge
    have hqEq : componentAttachmentCount C c =
        (componentAttachmentCount C c - 1) + 1 := by omega
    have hellEq : componentLongestPathLength C c =
        (componentLongestPathLength C c - 1) + 1 := by omega
    nlinarith [Nat.zero_le
      ((componentLongestPathLength C c - 1) *
        (componentAttachmentCount C c - 2))]
  have hupper : A.card ≤ C.length - s := by
    have hsubmono : C.length -
        (componentLongestPathLength C c + 1) *
          (componentAttachmentCount C c - 1) ≤ C.length - s :=
      Nat.sub_le_sub_left hprod C.length
    exact hcliqueBound.trans hsubmono
  omega

/-- Zero-longest-path branch of Ma--Ning edge Lemma (i).  The successor
set is independent, so a clique left after deleting `s-1` cycle vertices
contains all but at most one of those successors. -/
theorem terminal_component_weight_le_of_zero_and_clique
    (C : CycleWitness G) (hloc : IsLocallyMaximalCycle C)
    (hterminal : IsSwitchingTerminal G C)
    (c : (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (s : ℕ) (hs2 : 2 ≤ s) (S : Finset V)
    (hSsub : S ⊆ C.vertexFinset) (hScard : S.card = s - 1)
    (hclique : G.IsClique (↑(C.vertexFinset \ S) : Set V))
    (hell : componentLongestPathLength C c = 0) :
    componentWeight C c ≤ 2 * s := by
  have hUindep := componentSuccessorSet_isIndep_of_length_zero
    C hloc hterminal c hell
  have hUcard := indep_card_le_of_cycle_sdiff_clique C
    (componentSuccessorSet C c) S s
    (componentSuccessorSet_subset_cycle C c) hUindep
    hSsub hScard hclique hs2
  rw [componentSuccessorSet_card] at hUcard
  unfold componentWeight
  omega

/-- Ma--Ning edge lemma, part (i), proved from the Route-A literature
interface.  The closure and finite switching steps are explicit; the two
terminal-component branches are discharged above. -/
theorem maNing_edge_bound_i_of_literature
    (lit : LiteratureTheorems.{u})
    (C : CycleWitness G) (h2c : IsTwoConnected G)
    (hloc : IsLocallyMaximalCycle C)
    (hcn : C.length < Fintype.card V)
    (s : ℕ) (hs2 : 2 ≤ s)
    (hsUpper : s ≤ C.length / 2 - 1)
    (S : Finset V) (hSsub : S ⊆ C.vertexFinset)
    (hScard : S.card = s - 1)
    (hclique : (cycleClosure C).IsClique
      (↑(C.vertexFinset \ S) : Set V)) :
    G.edgeFinset.card ≤
      (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card +
        s * (Fintype.card V - C.length) := by
  classical
  let H := cycleClosure C
  obtain ⟨CH, hsameCH, hCHloc⟩ :=
    lit.closurePreservesLocalMaximality G C hloc
  have hH2c : IsTwoConnected H := by
    exact IsTwoConnected.mono (le_cycleClosure C) h2c
  obtain ⟨K, CK, hsameK, hK2c, hKloc, hcore, hedges, hterminal⟩ :=
    switching_terminal_structure_of_literature lit H CH hH2c hCHloc
  have hvH : CH.vertexFinset = C.vertexFinset := by
    simp [CycleWitness.vertexFinset, hsameCH.2.1]
  have hvK : CK.vertexFinset = C.vertexFinset := by
    calc
      CK.vertexFinset = CH.vertexFinset := by
        simp [CycleWitness.vertexFinset, hsameK.2.1]
      _ = C.vertexFinset := hvH
  have hlenH : CH.length = C.length := by
    simpa [CycleWitness.length] using
      (congrArg List.length hsameCH.2.1).symm
  have hlenK : CK.length = C.length := by
    have hKC : CK.length = CH.length := by
      simpa [CycleWitness.length] using
        (congrArg List.length hsameK.2.1).symm
    omega
  have hltK : CK.length < Fintype.card V := by omega
  obtain ⟨j, hmax, hbound⟩ :=
    switching_terminal_full_edge_bound lit CK hltK hterminal
  have hcoreC : K.induce (↑C.vertexFinset : Set V) =
      H.induce (↑C.vertexFinset : Set V) := by
    have hcore' := hcore
    rw [hvH] at hcore'
    exact hcore'
  have hSsubK : S ⊆ CK.vertexFinset := by simpa [hvK] using hSsub
  have hAcliqueK : K.IsClique (↑(CK.vertexFinset \ S) : Set V) := by
    rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    have ha' : a ∈ C.vertexFinset \ S := by simpa [hvK] using ha
    have hb' : b ∈ C.vertexFinset \ S := by simpa [hvK] using hb
    have hadjH := (SimpleGraph.isClique_iff H).mp hclique ha' hb' hab
    have haC : a ∈ C.vertexFinset := (Finset.mem_sdiff.mp ha').1
    have hbC : b ∈ C.vertexFinset := (Finset.mem_sdiff.mp hb').1
    change (K.induce (↑C.vertexFinset : Set V)).Adj
      ⟨a, haC⟩ ⟨b, hbC⟩
    rw [hcoreC]
    exact hadjH
  have hAcard : (CK.vertexFinset \ S).card = CK.length - s + 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSsubK,
      CK.card_vertexFinset]
    omega
  have hsK : s ≤ CK.length := by omega
  have hweight : componentWeight CK j ≤ 2 * s := by
    by_cases hell : componentLongestPathLength CK j = 0
    · exact terminal_component_weight_le_of_zero_and_clique
        CK hKloc hterminal j s hs2 S hSsubK hScard hAcliqueK hell
    · apply terminal_component_weight_le_of_positive_and_clique
        lit CK hK2c hKloc hterminal j s hs2 hsK (by omega)
        (CK.vertexFinset \ S) Finset.sdiff_subset hAcard hAcliqueK
  let extG :=
    (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
      (edgesBetween G (Finset.univ \ C.vertexFinset)
        C.vertexFinset).card
  let extH :=
    (H.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
      (edgesBetween H (Finset.univ \ C.vertexFinset)
        C.vertexFinset).card
  let extK :=
    (K.induce
      (↑(Finset.univ \ CK.vertexFinset) : Set V)).edgeFinset.card +
      (edgesBetween K (Finset.univ \ CK.vertexFinset)
        CK.vertexFinset).card
  have hextGH : extG = extH := by
    have houtGraph := cycleClosure_induce_outside_eq C
    have houtCard :
        (H.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card =
        (G.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card := by
      rw [← edgeSet_ncard_eq_edgeFinset_card,
        ← edgeSet_ncard_eq_edgeFinset_card]
      exact congrArg (fun J : SimpleGraph
        {x // x ∈ Finset.univ \ C.vertexFinset} => J.edgeSet.ncard)
          houtGraph
    have hcrossCard := congrArg Finset.card
      (cycleClosure_edgesBetween_outside_eq C)
    dsimp [extG, extH]
    rw [houtCard]
    simpa [H] using hcrossCard.symm
  have hdecH := edge_count_cycle_decomposition CH
  have hdecK := edge_count_cycle_decomposition CK
  have hinsideEq :
      (K.induce (↑CK.vertexFinset : Set V)).edgeFinset.card =
        (H.induce (↑C.vertexFinset : Set V)).edgeFinset.card := by
    rw [← edgeSet_ncard_eq_edgeFinset_card,
      ← edgeSet_ncard_eq_edgeFinset_card]
    rw [hvK]
    exact congrArg (fun J : SimpleGraph {x // x ∈ C.vertexFinset} =>
      J.edgeSet.ncard) hcoreC
  have hextHK : extH ≤ extK := by
    rw [hvH] at hdecH
    change H.edgeFinset.card =
      (H.induce (↑C.vertexFinset : Set V)).edgeFinset.card + extH at hdecH
    change K.edgeFinset.card =
      (K.induce (↑CK.vertexFinset : Set V)).edgeFinset.card + extK at hdecK
    rw [hinsideEq] at hdecK
    omega
  have hextK : extK ≤
      componentWeight CK j * (Fintype.card V - CK.length) / 2 := by
    change K.edgeFinset.card =
      (K.induce (↑CK.vertexFinset : Set V)).edgeFinset.card + extK at hdecK
    omega
  have hmul : componentWeight CK j *
      (Fintype.card V - CK.length) ≤
      (2 * s) * (Fintype.card V - CK.length) :=
    Nat.mul_le_mul_right _ hweight
  have hdiv := Nat.div_le_div_right hmul (c := 2)
  have hfactor : componentWeight CK j *
      (Fintype.card V - CK.length) / 2 ≤
      s * (Fintype.card V - CK.length) := by
    calc
      componentWeight CK j * (Fintype.card V - CK.length) / 2 ≤
          (2 * s) * (Fintype.card V - CK.length) / 2 := hdiv
      _ = s * (Fintype.card V - CK.length) := by
        rw [show (2 * s) * (Fintype.card V - CK.length) =
            (s * (Fintype.card V - CK.length)) * 2 by ac_rfl]
        exact Nat.mul_div_left _ (by decide)
  have hextG : extG ≤ s * (Fintype.card V - C.length) := by
    rw [hextGH, ← hlenK]
    exact hextHK.trans (hextK.trans hfactor)
  have hdecG := edge_count_cycle_decomposition C
  change G.edgeFinset.card =
    (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card + extG at hdecG
  rw [hdecG]
  exact Nat.add_le_add_left hextG _

/-- Ma--Ning edge lemma, part (ii), deduced from the explicit Route-A
literature interface and the verified switching/spacing argument. -/
theorem maNing_edge_bound_ii_of_literature
    (lit : LiteratureTheorems.{u})
    (C : CycleWitness G) (h2c : IsTwoConnected G)
    (hloc : IsLocallyMaximalCycle C)
    (hc4 : 4 ≤ C.length) (hcn : C.length < Fintype.card V) :
    (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
      (edgesBetween G (Finset.univ \ C.vertexFinset)
        C.vertexFinset).card ≤
      (C.length / 2) * (Fintype.card V - C.length) := by
  classical
  obtain ⟨K, CK, hsame, hK2c, hKloc, hcore, hedges, hterminal⟩ :=
    switching_terminal_structure_of_literature lit G C h2c hloc
  have hv : CK.vertexFinset = C.vertexFinset := by
    simp [CycleWitness.vertexFinset, hsame.2.1]
  have hlen : CK.length = C.length := by
    simpa [CycleWitness.length] using
      (congrArg List.length hsame.2.1).symm
  have hltK : CK.length < Fintype.card V := by omega
  obtain ⟨j, hmax, hbound⟩ :=
    switching_terminal_full_edge_bound lit CK hltK hterminal
  have hspacing := component_attachment_spacing
    CK hK2c hKloc hterminal j
  have hq2 := two_le_componentAttachmentCount CK hK2c j
  have hweight : componentWeight CK j ≤ 2 * (CK.length / 2) := by
    unfold componentWeight at *
    by_cases hell : componentLongestPathLength CK j = 0
    · rw [hell] at hspacing ⊢
      omega
    · have hellPos : 1 ≤ componentLongestPathLength CK j := by omega
      have hwlt : componentLongestPathLength CK j +
          2 * componentAttachmentCount CK j < CK.length := by
        nlinarith [hspacing]
      omega
  let extG :=
    (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
      (edgesBetween G (Finset.univ \ C.vertexFinset)
        C.vertexFinset).card
  let extK :=
    (K.induce
      (↑(Finset.univ \ CK.vertexFinset) : Set V)).edgeFinset.card +
      (edgesBetween K (Finset.univ \ CK.vertexFinset)
        CK.vertexFinset).card
  have hdecG := edge_count_cycle_decomposition C
  have hdecK := edge_count_cycle_decomposition CK
  have hinsideEq :
      (K.induce (↑CK.vertexFinset : Set V)).edgeFinset.card =
        (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card := by
    rw [hv]
    rw [← edgeSet_ncard_eq_edgeFinset_card,
      ← edgeSet_ncard_eq_edgeFinset_card]
    exact congrArg (fun H : SimpleGraph {x // x ∈ C.vertexFinset} =>
      H.edgeSet.ncard) hcore
  have hextGK : extG ≤ extK := by
    change G.edgeFinset.card =
      (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card + extG at hdecG
    change K.edgeFinset.card =
      (K.induce (↑CK.vertexFinset : Set V)).edgeFinset.card + extK at hdecK
    rw [hinsideEq] at hdecK
    omega
  have hextK : extK ≤
      componentWeight CK j * (Fintype.card V - CK.length) / 2 := by
    dsimp [extK]
    omega
  have hmul : componentWeight CK j * (Fintype.card V - CK.length) ≤
      (2 * (CK.length / 2)) * (Fintype.card V - CK.length) :=
    Nat.mul_le_mul_right _ hweight
  have hdiv := Nat.div_le_div_right hmul (c := 2)
  have hfactor :
      componentWeight CK j * (Fintype.card V - CK.length) / 2 ≤
        (CK.length / 2) * (Fintype.card V - CK.length) := by
    calc
      componentWeight CK j * (Fintype.card V - CK.length) / 2 ≤
          (2 * (CK.length / 2)) *
            (Fintype.card V - CK.length) / 2 := hdiv
      _ = (CK.length / 2) * (Fintype.card V - CK.length) := by
        rw [show (2 * (CK.length / 2)) *
            (Fintype.card V - CK.length) =
            ((CK.length / 2) * (Fintype.card V - CK.length)) * 2 by
              ac_rfl]
        exact Nat.mul_div_left _ (by decide)
  change extG ≤ (C.length / 2) * (Fintype.card V - C.length)
  rw [← hlen]
  exact hextGK.trans (hextK.trans hfactor)

end
end Erdos767
