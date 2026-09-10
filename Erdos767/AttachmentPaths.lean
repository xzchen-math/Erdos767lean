import Erdos767.CyclePacking

namespace Erdos767
open SimpleGraph
universe u
noncomputable section
set_option maxHeartbeats 800000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : SimpleGraph V} [DecidableRel K.Adj]

/-- In a terminal switched graph, two distinct cycle attachments can be
joined through the selected outside component by a path of length `ell+2`. -/
theorem exists_terminal_component_path
    (C : CycleWitness K) (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (x y : V)
    (hx : x ∈ setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset)
    (hy : y ∈ setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset)
    (hxy : x ≠ y) :
    ∃ p : K.Walk x y, p.IsPath ∧
      p.length = componentLongestPathLength C c + 2 ∧
      p.support.toFinset \ {x, y} ⊆ componentOutsideFinset C c := by
  classical
  let Q := componentOutsideFinset C c
  let D := componentLongestPathData C c
  let f := SimpleGraph.Embedding.induce (G := K) (↑Q : Set V)
  let pm : K.Walk (D.start : V) (D.finish : V) := D.path.map f.toHom
  have hQ := componentOutsideFinset_isComponent C c
  have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hx).1
  have hyC : y ∈ C.vertexFinset := (Finset.mem_filter.mp hy).1
  have hxAdj : K.Adj x (D.start : V) := by
    apply hterminal Q hQ x hxC
    · obtain ⟨z, hzQ, hxz⟩ := (Finset.mem_filter.mp hx).2
      exact ⟨z, hzQ, hxz⟩
    · exact D.start.property
  have hyAdj : K.Adj (D.finish : V) y := by
    have hyAll : K.Adj y (D.finish : V) := by
      apply hterminal Q hQ y hyC
      · obtain ⟨z, hzQ, hyz⟩ := (Finset.mem_filter.mp hy).2
        exact ⟨z, hzQ, hyz⟩
      · exact D.finish.property
    exact hyAll.symm
  have hxNotPm : x ∉ pm.support := by
    intro hxm
    change x ∈ (D.path.map f.toHom).support at hxm
    rw [SimpleGraph.Walk.support_map] at hxm
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hxm
    have hxQ : x ∈ Q := by
      simpa [f] using (hzx ▸ z.property)
    exact (Finset.mem_sdiff.mp (hQ.2.1 hxQ)).2 hxC
  have hyNotPm : y ∉ pm.support := by
    intro hym
    change y ∈ (D.path.map f.toHom).support at hym
    rw [SimpleGraph.Walk.support_map] at hym
    obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hym
    have hyQ : y ∈ Q := by
      simpa [f] using (hzy ▸ z.property)
    exact (Finset.mem_sdiff.mp (hQ.2.1 hyQ)).2 hyC
  let px : K.Walk x (D.finish : V) := pm.cons hxAdj
  have hpmPath : pm.IsPath := by
    dsimp [pm, f, Q]
    exact D.isPath.map (SimpleGraph.Embedding.induce
      (G := K) (↑(componentOutsideFinset C c) : Set V)).injective
  have hpxPath : px.IsPath := by
    exact hpmPath.cons hxNotPm
  have hyNotPx : y ∉ px.support := by
    intro hym
    simp only [px, SimpleGraph.Walk.support_cons, List.mem_cons] at hym
    rcases hym with hyx | hym
    · exact hxy hyx.symm
    · exact hyNotPm hym
  let p : K.Walk x y := px.concat hyAdj
  have hpPath : p.IsPath := hpxPath.concat hyNotPx hyAdj
  refine ⟨p, hpPath, ?_, ?_⟩
  · calc
      p.length = px.length + 1 := by
        simp only [p, SimpleGraph.Walk.length_concat]
      _ = pm.length + 2 := by simp [px]
      _ = D.path.length + 2 := by
        rw [show pm.length = D.path.length from D.path.length_map f.toHom]
      _ = componentLongestPathLength C c + 2 := by
        rfl
  · intro z hz
    have hzSupport : z ∈ p.support := by
      exact List.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1
    have hzEnds : z ≠ x ∧ z ≠ y := by
      simpa using (Finset.mem_sdiff.mp hz).2
    have hpSupport : p.support = x :: pm.support ++ [y] := by
      simp [p, px]
    rw [hpSupport] at hzSupport
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hzSupport
    rcases hzSupport with (rfl | hzMap) | rfl
    · exact (hzEnds.1 rfl).elim
    · change z ∈ (D.path.map f.toHom).support at hzMap
      rw [SimpleGraph.Walk.support_map] at hzMap
      obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hzMap
      have hzQ : z ∈ Q := by simpa [f] using (hwz ▸ w.property)
      exact hzQ
    · exact (hzEnds.2 rfl).elim

end
end Erdos767
