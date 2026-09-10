import Erdos767.AttachmentPacking

namespace Erdos767
open SimpleGraph
universe u
noncomputable section
set_option maxHeartbeats 1000000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : SimpleGraph V} [DecidableRel K.Adj]

def componentAttachmentList (C : CycleWitness K)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) : List V :=
  C.walk.support.dropLast.filter fun x =>
    x ∈ setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset

theorem mem_componentAttachmentList_iff
    (C : CycleWitness K)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (x : V) :
    x ∈ componentAttachmentList C c ↔
      x ∈ setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset := by
  classical
  constructor
  · intro hx
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  · intro hx
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hx⟩
    have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hx).1
    rw [← C.dropLast_support_toFinset] at hxC
    simpa using hxC

theorem length_componentAttachmentList
    (C : CycleWitness K)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    (componentAttachmentList C c).length = componentAttachmentCount C c := by
  classical
  calc
    (componentAttachmentList C c).length =
        (componentAttachmentList C c).toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup
        (C.isCycle.nodup_dropLast_support.filter _)
    _ = (setNeighborsIn K (componentOutsideFinset C c)
        C.vertexFinset).card := by
      congr 1
      ext x
      simp only [List.mem_toFinset]
      exact mem_componentAttachmentList_iff C c x
    _ = componentAttachmentCount C c := rfl

private theorem cyclicSuccessor_mem_ne {T : List V} (hT : T.Nodup)
    {x y : V} (hxy : IsCyclicSuccessor T x y) :
    x ∈ T ∧ y ∈ T ∧ x ≠ y := by
  rcases hxy with ⟨as, bs, h⟩ | ⟨middle, h⟩
  · subst T
    refine ⟨by simp, by simp, ?_⟩
    intro hxy
    subst y
    have hbad : [x, x].Nodup := hT.sublist (by simp)
    simpa using hbad
  · subst T
    refine ⟨by simp, by simp, ?_⟩
    intro hxy
    subst x
    simpa using hT

/-- A longest path through a terminal outside component is at least the
path obtained by adjoining two distinct cycle attachments to a longest
path inside that component. -/
theorem longest_path_through_component_lower
    (C : CycleWitness K) (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (x y : V)
    (hx : x ∈ setNeighborsIn K (componentOutsideFinset C c)
      C.vertexFinset)
    (hy : y ∈ setNeighborsIn K (componentOutsideFinset C c)
      C.vertexFinset)
    (hxy : x ≠ y) (p : K.Walk x y)
    (hp : IsLongestPathThrough (componentOutsideFinset C c) p) :
    componentLongestPathLength C c + 2 ≤ p.length := by
  classical
  obtain ⟨q, hqPath, hqLen, hqInside⟩ :=
    exists_terminal_component_path C hterminal c x y hx hy hxy
  have hQ := componentOutsideFinset_isComponent C c
  have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hx).1
  have hyC : y ∈ C.vertexFinset := (Finset.mem_filter.mp hy).1
  have hxNotQ : x ∉ componentOutsideFinset C c := fun hxQ =>
    (Finset.mem_sdiff.mp (hQ.2.1 hxQ)).2 hxC
  have hyNotQ : y ∉ componentOutsideFinset C c := fun hyQ =>
    (Finset.mem_sdiff.mp (hQ.2.1 hyQ)).2 hyC
  have hqThrough : IsPathThrough (componentOutsideFinset C c) q :=
    ⟨hqPath, hxNotQ, hyNotQ, hqInside⟩
  rw [← hqLen]
  exact hp.2 q hqThrough

/-- For positive longest-path length, the full cyclic list of component
attachments is a strong attachment in the sense used by Ma--Ning. -/
theorem componentAttachmentList_isStrong
    (C : CycleWitness K) (h2c : IsTwoConnected K)
    (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (hell : 1 ≤ componentLongestPathLength C c) :
    IsStrongAttachment C (componentOutsideFinset C c)
      (componentAttachmentList C c) := by
  classical
  let Q := componentOutsideFinset C c
  let T := componentAttachmentList C c
  let D := componentLongestPathData C c
  have hQ := componentOutsideFinset_isComponent C c
  have hnodup : T.Nodup := by
    exact C.isCycle.nodup_dropLast_support.filter _
  have hlength : T.length = componentAttachmentCount C c :=
    length_componentAttachmentList C c
  have hq2 := two_le_componentAttachmentCount C h2c c
  have hlisting : IsCyclicListing C T := by
    refine ⟨hnodup, by omega, C.walk.support.dropLast, ?_, ?_⟩
    · exact ⟨[], C.walk.support.dropLast, by simp, by simp⟩
    · exact List.filter_sublist
  refine ⟨hlisting, ?_⟩
  intro x y hsucc
  obtain ⟨hxT, hyT, hxy⟩ := cyclicSuccessor_mem_ne hnodup hsucc
  have hxAttach : x ∈ setNeighborsIn K Q C.vertexFinset := by
    simpa [T, Q] using (mem_componentAttachmentList_iff C c x).mp hxT
  have hyAttach : y ∈ setNeighborsIn K Q C.vertexFinset := by
    simpa [T, Q] using (mem_componentAttachmentList_iff C c y).mp hyT
  have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hxAttach).1
  have hyC : y ∈ C.vertexFinset := (Finset.mem_filter.mp hyAttach).1
  have huQ : (D.start : V) ∈ Q := D.start.property
  have hvQ : (D.finish : V) ∈ Q := D.finish.property
  have huv : (D.start : V) ≠ (D.finish : V) := by
    intro huv
    have hends : D.start = D.finish := Subtype.ext huv
    have hpNil : D.path.Nil := D.isPath.nil_iff_eq.mpr hends
    have hzero : D.path.length = 0 := hpNil.length_eq_zero
    change 1 ≤ D.path.length at hell
    omega
  have hxu : K.Adj x (D.start : V) := by
    apply hterminal Q hQ x hxC
    · obtain ⟨z, hzQ, hxz⟩ := (Finset.mem_filter.mp hxAttach).2
      exact ⟨z, hzQ, hxz⟩
    · exact huQ
  have hyv : K.Adj y (D.finish : V) := by
    apply hterminal Q hQ y hyC
    · obtain ⟨z, hzQ, hyz⟩ := (Finset.mem_filter.mp hyAttach).2
      exact ⟨z, hzQ, hyz⟩
    · exact hvQ
  refine ⟨(D.start : V), huQ, (D.finish : V), hvQ, hxu, hyv, ?_⟩
  apply Finset.disjoint_left.mpr
  intro z hzLeft hzRight
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft hzRight
  rcases hzLeft with hzLeft | hzLeft <;>
      rcases hzRight with hzRight | hzRight
  · exact hxy (hzLeft.symm.trans hzRight)
  · have hxv : x = (D.finish : V) := hzLeft.symm.trans hzRight
    exact (Finset.mem_sdiff.mp (hQ.2.1 hvQ)).2
      (hxv ▸ hxC)
  · have huy : (D.start : V) = y := hzLeft.symm.trans hzRight
    exact (Finset.mem_sdiff.mp (hQ.2.1 huQ)).2
      (huy.symm ▸ hyC)
  · exact huv (hzLeft.symm.trans hzRight)

end
end Erdos767
