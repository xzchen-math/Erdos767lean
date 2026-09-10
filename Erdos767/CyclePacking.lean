import Erdos767.CycleSplicing

namespace Erdos767
open SimpleGraph
universe u
noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem List.idxOf_drop_eq_sub_of_nodup {a b : V} {l : List V}
    (hl : l.Nodup) (ha : a ∈ l) (hb : b ∈ l)
    (hab : l.idxOf a ≤ l.idxOf b) :
    (l.drop (l.idxOf a)).idxOf b = l.idxOf b - l.idxOf a := by
  let ia := l.idxOf a
  let ib := l.idxOf b
  have hia : ia < l.length := by
    simpa [ia] using List.idxOf_lt_length_of_mem ha
  have hib : ib < l.length := by
    simpa [ib] using List.idxOf_lt_length_of_mem hb
  have hbDrop : b ∈ l.drop ia := by
    rw [List.mem_drop_iff_getElem]
    refine ⟨ib - ia, ?_, ?_⟩
    · omega
    · have hadd : ia + (ib - ia) = ib := by omega
      simpa only [hadd] using
        (List.getElem_idxOf (List.idxOf_lt_length_of_mem hb))
  have hidx : (l.drop ia).idxOf b < (l.drop ia).length :=
    List.idxOf_lt_length_of_mem hbDrop
  have hdiff : ib - ia < (l.drop ia).length := by
    simp only [List.length_drop]
    omega
  have hgetIdx := List.getElem_idxOf hidx
  have hgetDiff : (l.drop ia)[ib - ia] = b := by
    rw [List.getElem_drop]
    have hadd : ia + (ib - ia) = ib := by omega
    simpa only [hadd] using
      (List.getElem_idxOf (List.idxOf_lt_length_of_mem hb))
  have hnd : (l.drop ia).Nodup := hl.drop
  have heq := hnd.getElem_inj_iff.mp
    (hgetIdx.trans hgetDiff.symm)
  change (l.drop ia).idxOf b = ib - ia
  exact heq

theorem CycleWitness.rotate_takeUntil_length_eq_sub
    (C : CycleWitness G) (x y : V)
    (hx : x ∈ C.walk.support.dropLast)
    (hy : y ∈ C.walk.support.dropLast)
    (hxy : C.walk.support.dropLast.idxOf x <
      C.walk.support.dropLast.idxOf y) :
    ((C.walk.rotate x (List.mem_of_mem_dropLast hx)).takeUntil y (by
      apply (C.walk.mem_support_rotate_iff x _).mpr
      exact List.mem_of_mem_dropLast hy)).length =
      C.walk.support.dropLast.idxOf y -
        C.walk.support.dropLast.idxOf x := by
  let L := C.walk.support.dropLast
  let ix := L.idxOf x
  let iy := L.idxOf y
  have hxS : x ∈ C.walk.support := List.mem_of_mem_dropLast hx
  have hyS : y ∈ C.walk.support := List.mem_of_mem_dropLast hy
  have hxIdx : C.walk.support.idxOf x = ix := by
    rw [← C.walk.support_dropLast_concat C.isCycle.not_nil,
      C.walk.support_dropLast C.isCycle.not_nil]
    exact List.idxOf_append_of_mem (by simpa [L] using hx)
  have hyIdx : C.walk.support.idxOf y = iy := by
    rw [← C.walk.support_dropLast_concat C.isCycle.not_nil,
      C.walk.support_dropLast C.isCycle.not_nil]
    exact List.idxOf_append_of_mem (by simpa [L] using hy)
  have hix : ix < C.walk.length := by
    have := List.idxOf_lt_length_of_mem hx
    simpa [L, List.length_dropLast, C.walk.length_support] using this
  have hiy : iy < C.walk.length := by
    have := List.idxOf_lt_length_of_mem hy
    simpa [L, List.length_dropLast, C.walk.length_support] using this
  have hLlen : L.length = C.walk.length := by
    simp [L, List.length_dropLast, C.walk.length_support]
  have hxy' : ix < iy := by simpa [ix, iy, L] using hxy
  have hyDrop : y ∈ (C.walk.dropUntil x hxS).support := by
    rw [C.walk.dropUntil_eq_drop, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min]
    simp only [hxIdx]
    rw [Nat.min_eq_left (by omega)]
    rw [← C.walk.support_dropLast_concat C.isCycle.not_nil,
      C.walk.support_dropLast C.isCycle.not_nil]
    rw [List.drop_append_of_le_length (by
      simpa [L, ix, List.length_dropLast, C.walk.length_support] using
        Nat.le_of_lt hix)]
    apply List.mem_append_left
    rw [List.mem_drop_iff_getElem]
    refine ⟨iy - ix, ?_, ?_⟩
    · have hiyL : iy < L.length := by omega
      change iy - ix + ix < L.length
      omega
    · have hget := List.getElem_idxOf
        (List.idxOf_lt_length_of_mem hy)
      have hadd : ix + (iy - ix) = iy := by omega
      change L[ix + (iy - ix)] = y
      have hyL : y ∈ L := by simpa [L] using hy
      simpa only [hadd] using
        (List.getElem_idxOf (xs := L) (x := y)
          (List.idxOf_lt_length_of_mem hyL))
  change (((C.walk.dropUntil x hxS).append
    (C.walk.takeUntil x hxS)).takeUntil y _).length = _
  rw [SimpleGraph.Walk.takeUntil_append_of_mem_left _ _ hyDrop]
  rw [SimpleGraph.Walk.length_takeUntil]
  rw [C.walk.dropUntil_eq_drop, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min]
  simp only [hxIdx]
  rw [Nat.min_eq_left (by omega)]
  rw [← C.walk.support_dropLast_concat C.isCycle.not_nil,
    C.walk.support_dropLast C.isCycle.not_nil]
  rw [List.drop_append_of_le_length (by
    simpa [L, ix, List.length_dropLast, C.walk.length_support] using
      Nat.le_of_lt hix)]
  rw [List.idxOf_append_of_mem]
  · have hshift := List.idxOf_drop_eq_sub_of_nodup
      C.isCycle.nodup_dropLast_support hx hy (Nat.le_of_lt hxy)
    simpa [L, ix, iy] using hshift
  · rw [List.mem_drop_iff_getElem]
    refine ⟨iy - ix, ?_, ?_⟩
    · have hiyL : iy < L.length := by omega
      change iy - ix + ix < L.length
      omega
    · have hadd : ix + (iy - ix) = iy := by omega
      change L[ix + (iy - ix)] = y
      have hyL : y ∈ L := by simpa [L] using hy
      simpa only [hadd] using
        (List.getElem_idxOf (xs := L) (x := y)
          (List.idxOf_lt_length_of_mem hyL))

theorem CycleWitness.support_rotate_dropLast_eq
    (C : CycleWitness G) (x : V)
    (hx : x ∈ C.walk.support.dropLast) :
    (C.walk.rotate x (List.mem_of_mem_dropLast hx)).support.dropLast =
      C.walk.support.dropLast.drop
          (C.walk.support.dropLast.idxOf x) ++
        C.walk.support.dropLast.take
          (C.walk.support.dropLast.idxOf x) := by
  let L := C.walk.support.dropLast
  let ix := L.idxOf x
  have hxS : x ∈ C.walk.support := List.mem_of_mem_dropLast hx
  have hxIdx : C.walk.support.idxOf x = ix := by
    rw [← C.walk.support_dropLast_concat C.isCycle.not_nil,
      C.walk.support_dropLast C.isCycle.not_nil]
    exact List.idxOf_append_of_mem (by simpa [L] using hx)
  have hix : ix < C.walk.length := by
    have := List.idxOf_lt_length_of_mem hx
    simpa [L, List.length_dropLast, C.walk.length_support] using this
  have hLlen : L.length = C.walk.length := by
    simp [L, List.length_dropLast, C.walk.length_support]
  rw [SimpleGraph.Walk.rotate]
  rw [SimpleGraph.Walk.support_append_eq_support_dropLast_append]
  rw [C.walk.dropUntil_eq_drop, C.walk.takeUntil_eq_take]
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    SimpleGraph.Walk.support_take, hxIdx]
  simp only [Nat.min_eq_left (Nat.le_of_lt hix)]
  rw [← C.walk.support_dropLast_concat C.isCycle.not_nil,
    C.walk.support_dropLast C.isCycle.not_nil]
  rw [List.drop_append_of_le_length (by
    simpa [L, ix, List.length_dropLast, C.walk.length_support] using
      Nat.le_of_lt hix)]
  simp only [List.dropLast_append_cons, List.dropLast_singleton,
    List.append_nil]
  have htake : (L ++ [C.base]).take (ix + 1) = L.take (ix + 1) := by
    rw [List.take_append_of_le_length]
    omega
  rw [htake]
  have hdropLastTake : (L.take (ix + 1)).dropLast = L.take ix := by
    rw [List.dropLast_eq_take, List.length_take]
    rw [Nat.min_eq_left (by omega)]
    simp only [Nat.add_sub_cancel]
    simp [List.take_take, Nat.min_eq_left (Nat.le_succ ix)]
  have htakeNonempty : L.take (ix + 1) ≠ [] := by
    intro hempty
    rw [List.take_eq_nil_iff] at hempty
    rcases hempty with hzero | hLnil
    · omega
    · have hxL : x ∈ L := by simpa [L] using hx
      rw [hLnil] at hxL
      simp at hxL
  change (L.drop ix ++ L.take (ix + 1)).dropLast =
    L.drop ix ++ L.take ix
  rw [List.dropLast_append_of_ne_nil htakeNonempty]
  rw [hdropLastTake]

theorem CycleWitness.rotate_takeUntil_length_eq_wrap
    (C : CycleWitness G) (x y : V)
    (hx : x ∈ C.walk.support.dropLast)
    (hy : y ∈ C.walk.support.dropLast)
    (hyx : C.walk.support.dropLast.idxOf y <
      C.walk.support.dropLast.idxOf x) :
    ((C.walk.rotate x (List.mem_of_mem_dropLast hx)).takeUntil y (by
      apply (C.walk.mem_support_rotate_iff x _).mpr
      exact List.mem_of_mem_dropLast hy)).length =
      C.length - C.walk.support.dropLast.idxOf x +
        C.walk.support.dropLast.idxOf y := by
  let L := C.walk.support.dropLast
  let ix := L.idxOf x
  let iy := L.idxOf y
  have hxS : x ∈ C.walk.support := List.mem_of_mem_dropLast hx
  have hyS : y ∈ C.walk.support := List.mem_of_mem_dropLast hy
  let r : G.Walk x x := C.walk.rotate x hxS
  have hyR : y ∈ r.support :=
    (C.walk.mem_support_rotate_iff x hxS).mpr hyS
  have hLlen : L.length = C.length := by
    simp [L, CycleWitness.length, List.length_dropLast,
      C.walk.length_support]
  have hix : ix < L.length := List.idxOf_lt_length_of_mem (by
    simpa [L] using hx)
  have hiy : iy < L.length := List.idxOf_lt_length_of_mem (by
    simpa [L] using hy)
  have hyx' : iy < ix := by simpa [iy, ix, L] using hyx
  have hyTake : y ∈ L.take ix := by
    rw [List.mem_take_iff_idxOf_lt (by simpa [L] using hy)]
    simpa [iy]
  have hyNotDrop : y ∉ L.drop ix := by
    intro hyDrop
    rw [List.mem_drop_iff_getElem] at hyDrop
    obtain ⟨j, hjlt, hjy⟩ := hyDrop
    have hgetY : L[iy] = y :=
      List.getElem_idxOf (by simpa [iy] using hiy)
    have heq : ix + j = iy :=
      C.isCycle.nodup_dropLast_support.getElem_inj_iff.mp
        (hjy.trans hgetY.symm)
    omega
  have hyDropLast : y ∈ r.support.dropLast := by
    rw [CycleWitness.support_rotate_dropLast_eq C x hx]
    exact List.mem_append_right _ hyTake
  rw [SimpleGraph.Walk.length_takeUntil]
  have hsupport : r.support = r.support.dropLast ++ [x] := by
    symm
    simpa using r.support_dropLast_concat
      ((C.isCycle.rotate hxS).not_nil)
  rw [hsupport, List.idxOf_append_of_mem hyDropLast]
  rw [CycleWitness.support_rotate_dropLast_eq C x hx]
  rw [List.idxOf_append_of_notMem hyNotDrop]
  have hidxTake : (L.take ix).idxOf y = iy := by
    exact (List.take_prefix ix L).idxOf_eq_of_mem hyTake
  rw [hidxTake, List.length_drop]
  simpa [L, ix, iy, hLlen, CycleWitness.length] using
    (show L.length - ix + iy = L.length - ix + iy from rfl)

end
end Erdos767
