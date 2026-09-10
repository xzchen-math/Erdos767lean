import Erdos767.AttachmentCount

namespace Erdos767
open SimpleGraph
universe u
noncomputable section
set_option maxHeartbeats 1200000

def listLastFrom (a : ℕ) : List ℕ → ℕ
  | [] => a
  | b :: l => listLastFrom b l

theorem listLastFrom_mem (a : ℕ) : ∀ l, listLastFrom a l ∈ a :: l := by
  intro l
  induction l generalizing a with
  | nil => simp [listLastFrom]
  | cons b l ih =>
      change listLastFrom b l ∈ a :: b :: l
      exact List.mem_cons_of_mem a (ih b)

theorem listLastFrom_mem_tail (a : ℕ) {l : List ℕ} (hne : l ≠ []) :
    listLastFrom a l ∈ l := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons b l =>
      simp only [listLastFrom]
      exact listLastFrom_mem b l

theorem sorted_head_lt_listLastFrom (a : ℕ) (l : List ℕ)
    (hsort : (a :: l).Pairwise (· < ·)) (hne : l ≠ []) :
    a < listLastFrom a l := by
  have hmemTail : listLastFrom a l ∈ l :=
    listLastFrom_mem_tail a hne
  exact (List.pairwise_cons.mp hsort).1 _ hmemTail

theorem sorted_gap_last_aux (d : ℕ) :
    ∀ (a : ℕ) (l : List ℕ),
      (a :: l).Pairwise (· < ·) →
      (∀ x ∈ a :: l, ∀ y ∈ a :: l, x < y → x + d ≤ y) →
      a + ((a :: l).length - 1) * d ≤ listLastFrom a l := by
  intro a l
  induction l generalizing a with
  | nil => simp [listLastFrom]
  | cons b l ih =>
      intro hsort hgap
      have hablt : a < b :=
        (List.pairwise_cons.mp hsort).1 b (by simp)
      have hab : a + d ≤ b :=
        hgap a (by simp) b (by simp) hablt
      have htailSort : (b :: l).Pairwise (· < ·) :=
        (List.pairwise_cons.mp hsort).2
      have htailGap : ∀ x ∈ b :: l, ∀ y ∈ b :: l,
          x < y → x + d ≤ y := by
        intro x hx y hy hxy
        exact hgap x (by simp [hx]) y (by simp [hy]) hxy
      have htail := ih b htailSort htailGap
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.succ_mul,
        listLastFrom] at htail ⊢
      omega

theorem sorted_gap_mul_length_le
    (c d a : ℕ) (l : List ℕ)
    (hsort : (a :: l).Pairwise (· < ·))
    (hgap : ∀ x ∈ a :: l, ∀ y ∈ a :: l,
      x < y → x + d ≤ y)
    (hwrap : listLastFrom a l + d ≤ c + a) :
    (a :: l).length * d ≤ c := by
  have hlast := sorted_gap_last_aux d a l hsort hgap
  simp only [List.length_cons, Nat.add_sub_cancel, Nat.succ_mul] at hlast ⊢
  omega

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : SimpleGraph V} [DecidableRel K.Adj]

/-- The cyclic spacing inequality in Ma--Ning edge Lemma (ii): if `ell` is
the longest path length in an outside component and `q` its number of
cycle attachments, then `(ell+2)q ≤ c`. -/
theorem component_attachment_spacing
    (C : CycleWitness K) (h2c : IsTwoConnected K)
    (hloc : IsLocallyMaximalCycle C)
    (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    (componentLongestPathLength C c + 2) *
        componentAttachmentCount C c ≤ C.length := by
  classical
  let L := C.walk.support.dropLast
  let T := setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset
  let P : Finset ℕ := T.image fun x => L.idxOf x
  let d := componentLongestPathLength C c + 2
  have hTcard : 2 ≤ T.card := by
    simpa [T, componentAttachmentCount] using
      two_le_componentAttachmentCount C h2c c
  have hindexInj : Set.InjOn (fun x : V => L.idxOf x) (↑T : Set V) := by
    intro x hx y hy hidx
    have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hx).1
    have hyC : y ∈ C.vertexFinset := (Finset.mem_filter.mp hy).1
    have hxL : x ∈ L := by
      rw [← C.dropLast_support_toFinset] at hxC
      simpa [L] using hxC
    have hyL : y ∈ L := by
      rw [← C.dropLast_support_toFinset] at hyC
      simpa [L] using hyC
    exact (List.idxOf_inj hxL).mp hidx
  have hPcard : P.card = T.card := by
    exact Finset.card_image_iff.mpr hindexInj
  have hsortLen : (P.sort (· ≤ ·)).length = T.card := by
    rw [Finset.length_sort, hPcard]
  have hsortPair : (P.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort P).pairwise
  cases hs : P.sort (· ≤ ·) with
  | nil =>
      rw [hs] at hsortLen
      simp at hsortLen
      omega
  | cons a l =>
      have hsort : (a :: l).Pairwise (· < ·) := by
        simpa [hs] using hsortPair
      have hlen : (a :: l).length = T.card := by
        simpa [hs] using hsortLen
      have hlNonempty : l ≠ [] := by
        intro hl
        subst l
        simp at hlen
        omega
      have hgap : ∀ i ∈ a :: l, ∀ j ∈ a :: l,
          i < j → i + d ≤ j := by
        intro i hi j hj hij
        have hiP : i ∈ P := by
          rw [← Finset.mem_sort (r := (· ≤ ·))]
          simpa [hs] using hi
        have hjP : j ∈ P := by
          rw [← Finset.mem_sort (r := (· ≤ ·))]
          simpa [hs] using hj
        obtain ⟨x, hxT, hxi⟩ := Finset.mem_image.mp hiP
        obtain ⟨y, hyT, hyj⟩ := Finset.mem_image.mp hjP
        have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hxT).1
        have hyC : y ∈ C.vertexFinset := (Finset.mem_filter.mp hyT).1
        have hxL : x ∈ L := by
          rw [← C.dropLast_support_toFinset] at hxC
          simpa [L] using hxC
        have hyL : y ∈ L := by
          rw [← C.dropLast_support_toFinset] at hyC
          simpa [L] using hyC
        have hxy : x ≠ y := by
          intro hxy
          subst y
          omega
        obtain ⟨p, hp, hplen, hpQ⟩ :=
          exists_terminal_component_path C hterminal c x y hxT hyT hxy
        have hpout : p.support.toFinset \ {x, y} ⊆
            Finset.univ \ C.vertexFinset := fun _ hz =>
          (componentOutsideFinset_isComponent C c).2.1 (hpQ hz)
        have harc := external_path_le_rotated_cycle_arc
          C hloc x y hxC hyC hxy p hp hpout
        have harcLen := C.rotate_takeUntil_length_eq_sub x y hxL hyL (by
          simpa [L, hxi, hyj] using hij)
        rw [harcLen, hplen] at harc
        have hxidx : C.walk.support.dropLast.idxOf x = i := by
          simpa [L] using hxi
        have hyidx : C.walk.support.dropLast.idxOf y = j := by
          simpa [L] using hyj
        rw [hxidx, hyidx] at harc
        dsimp [d]
        omega
      have haMem : a ∈ P := by
        rw [← Finset.mem_sort (r := (· ≤ ·))]
        simp [hs]
      have hlastMemList : listLastFrom a l ∈ a :: l :=
        listLastFrom_mem a l
      have hlastMem : listLastFrom a l ∈ P := by
        rw [← Finset.mem_sort (r := (· ≤ ·))]
        simpa [hs] using hlastMemList
      obtain ⟨x, hxT, hxlast⟩ := Finset.mem_image.mp hlastMem
      obtain ⟨y, hyT, hyfirst⟩ := Finset.mem_image.mp haMem
      have hxC : x ∈ C.vertexFinset := (Finset.mem_filter.mp hxT).1
      have hyC : y ∈ C.vertexFinset := (Finset.mem_filter.mp hyT).1
      have hxL : x ∈ L := by
        rw [← C.dropLast_support_toFinset] at hxC
        simpa [L] using hxC
      have hyL : y ∈ L := by
        rw [← C.dropLast_support_toFinset] at hyC
        simpa [L] using hyC
      have hfirstLast : a < listLastFrom a l :=
        sorted_head_lt_listLastFrom a l hsort hlNonempty
      have hxy : x ≠ y := by
        intro hxy
        subst y
        omega
      obtain ⟨p, hp, hplen, hpQ⟩ :=
        exists_terminal_component_path C hterminal c x y hxT hyT hxy
      have hpout : p.support.toFinset \ {x, y} ⊆
          Finset.univ \ C.vertexFinset := fun _ hz =>
        (componentOutsideFinset_isComponent C c).2.1 (hpQ hz)
      have harc := external_path_le_rotated_cycle_arc
        C hloc x y hxC hyC hxy p hp hpout
      have harcLen := C.rotate_takeUntil_length_eq_wrap x y hxL hyL (by
        simpa [L, hxlast, hyfirst] using hfirstLast)
      rw [harcLen, hplen] at harc
      have hxidx : C.walk.support.dropLast.idxOf x = listLastFrom a l := by
        simpa [L] using hxlast
      have hyidx : C.walk.support.dropLast.idxOf y = a := by
        simpa [L] using hyfirst
      rw [hxidx, hyidx] at harc
      have hxIndexLt : C.walk.support.dropLast.idxOf x < C.length := by
        have hmem := List.idxOf_lt_length_of_mem hxL
        simpa [L, CycleWitness.length, List.length_dropLast,
          C.walk.length_support] using hmem
      have hwrap : listLastFrom a l + d ≤ C.length + a := by
        dsimp [d]
        omega
      have hpacked := sorted_gap_mul_length_le C.length d a l hsort hgap hwrap
      dsimp [d] at hpacked ⊢
      have hlen' : l.length + 1 = T.card := by simpa using hlen
      rw [hlen'] at hpacked
      simpa [T, componentAttachmentCount, Nat.mul_comm] using hpacked

end
end Erdos767
