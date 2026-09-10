import Erdos767.ExteriorComponents

/-!
# Cycle splicing under local maximality

The main theorem constructs the replacement cycle as an actual Mathlib walk
and verifies the manuscript's two-crossing-edge condition.
-/

namespace Erdos767
open SimpleGraph
universe u
noncomputable section
set_option maxHeartbeats 800000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path whose internal vertices lie outside a locally maximal cycle
cannot be longer than either of the two cycle arcs with the same endpoints. -/
theorem external_path_le_rotated_cycle_arc
    (C : CycleWitness G) (hloc : IsLocallyMaximalCycle C)
    (x y : V) (hx : x ∈ C.vertexFinset) (hy : y ∈ C.vertexFinset)
    (hxy : x ≠ y) (p : G.Walk x y) (hp : p.IsPath)
    (hinternal : p.support.toFinset \ {x, y} ⊆
      Finset.univ \ C.vertexFinset) :
    p.length ≤ ((C.walk.rotate x (by
      simpa [CycleWitness.vertexFinset] using hx)).takeUntil y (by
        apply (C.walk.mem_support_rotate_iff x (by
          simpa [CycleWitness.vertexFinset] using hx)).mpr
        simpa [CycleWitness.vertexFinset] using hy)).length := by
  classical
  let hxS : x ∈ C.walk.support := by
    simpa [CycleWitness.vertexFinset] using hx
  let r : G.Walk x x := C.walk.rotate x hxS
  have hrCycle : r.IsCycle := C.isCycle.rotate hxS
  have hyR : y ∈ r.support := by
    apply (C.walk.mem_support_rotate_iff x hxS).mpr
    simpa [CycleWitness.vertexFinset] using hy
  let A : G.Walk x y := r.takeUntil y hyR
  let B : G.Walk y x := r.dropUntil y hyR
  change p.length ≤ A.length
  by_contra hlong
  have hApos : 0 < A.length := by
    have hnotNil : ¬ A.Nil := SimpleGraph.Walk.not_nil_of_ne hxy
    have hne : A.length ≠ 0 := by
      simpa [SimpleGraph.Walk.length_eq_zero_iff] using hnotNil
    omega
  have hAB : A.append B = r := r.take_spec hyR
  have hABCycle : (A.append B).IsCycle := by
    rw [hAB]
    exact hrCycle
  have hAPath : A.IsPath := hrCycle.isPath_takeUntil hyR
  have hBPath : B.IsPath :=
    hABCycle.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne hxy)
  have hBNotNil : ¬ B.Nil := SimpleGraph.Walk.not_nil_of_ne hxy.symm
  have hBsupport : ∀ z ∈ B.support, z ∈ C.vertexFinset := by
    intro z hzB
    have hzR : z ∈ r.support := r.support_dropUntil_subset_support hyR hzB
    have hzC : z ∈ C.walk.support :=
      (C.walk.mem_support_rotate_iff x hxS).mp hzR
    simpa [CycleWitness.vertexFinset] using hzC
  have hxNotTail : x ∉ p.support.tail := by
    have hnodup : (x :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hyNotBTail : y ∉ B.support.tail := by
    have hnodup : (y :: B.support.tail).Nodup := by
      rw [B.cons_tail_support]
      exact hBPath.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisj : p.support.tail.Disjoint B.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzB
    have hzC : z ∈ C.vertexFinset := hBsupport z (by
      exact List.mem_of_mem_tail hzB)
    have hzx : z ≠ x := by
      intro hzx
      subst z
      exact hxNotTail hzp
    have hzy : z ≠ y := by
      intro hzy
      subst z
      exact hyNotBTail hzB
    have hzInt : z ∈ p.support.toFinset \ {x, y} := by
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa using List.mem_of_mem_tail hzp
      · simp [hzx, hzy]
    have hzOut := hinternal hzInt
    exact (Finset.mem_sdiff.mp hzOut).2 hzC
  have hpLong : 1 < p.length := by omega
  let Dwalk : G.Walk x x := p.append B
  have hDcycle : Dwalk.IsCycle := by
    exact hp.isCycle_append hBPath hdisj (Or.inl hpLong)
  let D : CycleWitness G := ⟨x, Dwalk, hDcycle⟩
  have hlengthAB : A.length + B.length = C.length := by
    have hlen := congrArg SimpleGraph.Walk.length hAB
    simpa [SimpleGraph.Walk.length_append, r, CycleWitness.length] using hlen
  have hDlong : C.length < D.length := by
    change C.length < (p.append B).length
    rw [SimpleGraph.Walk.length_append]
    omega
  have hcrossSub : cycleCrossingEdges C D ⊆
      {s(x, p.snd), s(y, p.penultimate)} := by
    intro e heCross
    have heD := (Finset.mem_inter.mp heCross).1
    have heAcross := (Finset.mem_inter.mp heCross).2
    have heList : e ∈ Dwalk.edges := by
      simpa [D, CycleWitness.edgeFinset] using heD
    rw [SimpleGraph.Walk.edges_append] at heList
    have heCases : e ∈ p.edges ∨ e ∈ B.edges := by simpa using heList
    unfold edgesBetween at heAcross
    obtain ⟨heG, a, haC, b, hbOut, hab⟩ := Finset.mem_filter.mp heAcross
    rcases heCases with hep | heB
    · rw [hab] at hep
      have haSupport : a ∈ p.support := p.fst_mem_support_of_mem_edges hep
      have haEnds : a = x ∨ a = y := by
        by_contra hEnds
        push Not at hEnds
        have haInt : a ∈ p.support.toFinset \ {x, y} := by
          apply Finset.mem_sdiff.mpr
          exact ⟨by simpa using haSupport, by simp [hEnds.1, hEnds.2]⟩
        have haOut := hinternal haInt
        exact (Finset.mem_sdiff.mp haOut).2 haC
      rcases haEnds with rfl | rfl
      · have hbEq : b = p.snd := hp.eq_snd_of_mem_edges hep
        simp [hab, hbEq]
      · have hbEq : b = p.penultimate := hp.eq_penultimate_of_mem_edges hep
        simp [hab, hbEq]
    · rw [hab] at heB
      have hbSupport : b ∈ B.support := B.snd_mem_support_of_mem_edges heB
      have hbC := hBsupport b hbSupport
      exact ((Finset.mem_sdiff.mp hbOut).2 hbC).elim
  have hcrossUpper : (cycleCrossingEdges C D).card ≤ 2 := by
    exact (Finset.card_le_card hcrossSub).trans Finset.card_le_two
  have hcrossLower := hloc D hDlong
  omega

end
end Erdos767
