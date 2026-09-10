import Erdos767.StrongAttachment
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace Erdos767
open SimpleGraph
universe u
noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def cycleSuccessor (C : CycleWitness G) : Equiv.Perm V :=
  C.walk.support.dropLast.formPerm

theorem cycleSuccessor_mem (C : CycleWitness G) {x : V}
    (hx : x ∈ C.vertexFinset) : cycleSuccessor C x ∈ C.vertexFinset := by
  have hxL : x ∈ C.walk.support.dropLast := by
    rw [← C.dropLast_support_toFinset] at hx
    simpa using hx
  have hs := List.formPerm_apply_mem_of_mem (l := C.walk.support.dropLast) hxL
  rw [← C.dropLast_support_toFinset]
  simpa [cycleSuccessor] using hs

theorem cycleSuccessor_eq_rotate_snd (C : CycleWitness G) {x : V}
    (hx : x ∈ C.vertexFinset) :
    cycleSuccessor C x = (C.walk.rotate x (by
      simpa [CycleWitness.vertexFinset] using hx)).snd := by
  let L := C.walk.support.dropLast
  have hxL : x ∈ L := by
    rw [← C.dropLast_support_toFinset] at hx
    simpa [L] using hx
  let hxS : x ∈ C.walk.support := List.mem_of_mem_dropLast hxL
  let r : G.Walk x x := C.walk.rotate x hxS
  have hrCycle : r.IsCycle := C.isCycle.rotate hxS
  have hrDrop : r.support.dropLast = L.rotate (L.idxOf x) := by
    rw [CycleWitness.support_rotate_dropLast_eq C x hxL]
    rw [List.rotate_eq_drop_append_take]
    exact (List.idxOf_le_length (a := x) (l := L))
  have hdropLen : 1 < r.support.dropLast.length := by
    rw [hrDrop, List.length_rotate]
    have hLlen : L.length = C.length := by
      simp [L, CycleWitness.length, List.length_dropLast,
        C.walk.length_support]
    have hc3 : 3 ≤ C.length := C.isCycle.three_le_length
    omega
  have hsnd : r.snd = r.support.dropLast[1] := by
    rw [r.snd_eq_support_getElem_one hrCycle.not_nil]
    exact (List.getElem_dropLast hdropLen).symm
  have hnext := List.formPerm_apply_mem_eq_next
    C.isCycle.nodup_dropLast_support x hxL
  rw [List.next_eq_getElem] at hnext
  rw [show cycleSuccessor C x = L.formPerm x by rfl, hnext, hsnd]
  have hrotLen : 1 < (L.rotate (L.idxOf x)).length := by
    rw [← hrDrop]
    exact hdropLen
  have hrGet := congrArg (fun l : List V => l[1]?) hrDrop
  have hrElem : (L.rotate (L.idxOf x))[1] = r.support.dropLast[1] := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem hrotLen).symm.trans
      (hrGet.symm.trans (List.getElem?_eq_getElem hdropLen))
  rw [← hrElem, List.getElem_rotate]
  simp only [L, Nat.add_comm]

theorem cycleSuccessor_ne_of_external_two_path
    (C : CycleWitness G) (hloc : IsLocallyMaximalCycle C)
    {x y : V} (hx : x ∈ C.vertexFinset) (hy : y ∈ C.vertexFinset)
    (hxy : x ≠ y) (p : G.Walk x y) (hp : p.IsPath)
    (hplen : p.length = 2)
    (hpout : p.support.toFinset \ {x, y} ⊆
      Finset.univ \ C.vertexFinset) :
    cycleSuccessor C x ≠ y := by
  intro hsucc
  have harc := external_path_le_rotated_cycle_arc
    C hloc x y hx hy hxy p hp hpout
  let hxS : x ∈ C.walk.support := by
    simpa [CycleWitness.vertexFinset] using hx
  let r : G.Walk x x := C.walk.rotate x hxS
  have hrCycle : r.IsCycle := C.isCycle.rotate hxS
  have hyR : y ∈ r.support := by
    apply (C.walk.mem_support_rotate_iff x hxS).mpr
    simpa [CycleWitness.vertexFinset] using hy
  have hsnd : r.snd = y := by
    rw [← hsucc]
    exact (cycleSuccessor_eq_rotate_snd C hx).symm
  have hsndNe : r.snd ≠ x := (r.adj_snd hrCycle.not_nil).ne.symm
  have hidx : r.support.idxOf y = 1 := by
    rw [← hsnd]
    rw [← r.cons_support_tail hrCycle.not_nil]
    have htail : r.tail.support = r.snd :: r.tail.support.tail :=
      (r.tail.cons_tail_support).symm
    rw [List.idxOf_cons_ne _ hsndNe.symm]
    have hin : r.tail.support.idxOf r.snd = 0 := by
      apply (List.idxOf_eq_zero_iff_eq_nil_or_head_eq r.snd).2
      right
      rw [htail]
      rfl
    rw [hin]
  change p.length ≤ (r.takeUntil y hyR).length at harc
  rw [r.length_takeUntil, hidx, hplen] at harc
  omega

/-- Deleting the two forward cycle edges at `x,y` and adding a chord
between their successors leaves a path from `y` to `x` through all cycle
vertices. -/
theorem exists_successor_chord_complement_path
    (C : CycleWitness G) {x y : V}
    (hx : x ∈ C.vertexFinset) (hy : y ∈ C.vertexFinset)
    (hxy : x ≠ y)
    (hax : cycleSuccessor C x ≠ y)
    (hby : cycleSuccessor C y ≠ x)
    (hab : G.Adj (cycleSuccessor C x) (cycleSuccessor C y)) :
    ∃ q : G.Walk y x, q.IsPath ∧ q.length = C.length - 1 ∧
      ∀ z ∈ q.support, z ∈ C.vertexFinset := by
  classical
  let hxS : x ∈ C.walk.support := by
    simpa [CycleWitness.vertexFinset] using hx
  let r : G.Walk x x := C.walk.rotate x hxS
  have hrCycle : r.IsCycle := C.isCycle.rotate hxS
  have hyR : y ∈ r.support := by
    apply (C.walk.mem_support_rotate_iff x hxS).mpr
    simpa [CycleWitness.vertexFinset] using hy
  let P : G.Walk x y := r.takeUntil y hyR
  let D : G.Walk y x := r.dropUntil y hyR
  have hPD : P.append D = r := r.take_spec hyR
  have hPnotNil : ¬ P.Nil := SimpleGraph.Walk.not_nil_of_ne hxy
  have hDnotNil : ¬ D.Nil := SimpleGraph.Walk.not_nil_of_ne hxy.symm
  have hPPath : P.IsPath := hrCycle.isPath_takeUntil hyR
  have hDPath : D.IsPath := by
    have hcyc : (P.append D).IsCycle := by rw [hPD]; exact hrCycle
    exact hcyc.isPath_of_append_right hPnotNil
  have htailNodup : (P.support.tail ++ D.support.tail).Nodup := by
    rw [← SimpleGraph.Walk.tail_support_append, hPD]
    exact hrCycle.support_nodup
  have hdisjPD : P.support.tail.Disjoint D.support.tail :=
    List.disjoint_of_nodup_append htailNodup
  let A : G.Walk P.snd y := P.tail
  let B : G.Walk D.snd x := D.tail
  have hAPath : A.IsPath := by
    dsimp [A]
    exact hPPath.drop 1
  have hBPath : B.IsPath := by
    dsimp [B]
    exact hDPath.drop 1
  have haEq : P.snd = cycleSuccessor C x := by
    have hsndP : P.snd = r.snd := by
      exact r.snd_takeUntil hxy.symm hyR
    rw [hsndP]
    exact (cycleSuccessor_eq_rotate_snd C hx).symm
  have hrDrop : r.support.dropLast =
      C.walk.support.dropLast.rotate
        (C.walk.support.dropLast.idxOf x) := by
    have hxL : x ∈ C.walk.support.dropLast := by
      rw [← C.dropLast_support_toFinset] at hx
      simpa using hx
    rw [CycleWitness.support_rotate_dropLast_eq C x hxL]
    rw [List.rotate_eq_drop_append_take]
    exact List.idxOf_le_length
  let Cr : CycleWitness G := ⟨x, r, hrCycle⟩
  have hsuccEq : cycleSuccessor Cr = cycleSuccessor C := by
    change r.support.dropLast.formPerm =
      C.walk.support.dropLast.formPerm
    rw [hrDrop]
    exact List.formPerm_rotate C.walk.support.dropLast
      C.isCycle.nodup_dropLast_support _
  have hyCr : y ∈ Cr.vertexFinset := by
    change y ∈ r.support.toFinset
    simpa using hyR
  have hbRot := cycleSuccessor_eq_rotate_snd Cr hyCr
  have hrotSnd : (r.rotate y hyR).snd = D.snd := by
    change (D.append P).snd = D.snd
    have hDpos : 0 < D.length := by
      simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hDnotNil
    by_cases hD1 : D.length = 1
    · simp only [SimpleGraph.Walk.snd,
        SimpleGraph.Walk.getVert_append, hD1, lt_self_iff_false,
        ↓reduceIte, Nat.sub_self]
      rw [P.getVert_zero]
      rw [← hD1]
      exact D.getVert_length.symm
    · have hD2 : 1 < D.length := by omega
      simp [SimpleGraph.Walk.snd,
        SimpleGraph.Walk.getVert_append, hD2]
  have hbEq : D.snd = cycleSuccessor C y := by
    rw [← hsuccEq]
    rw [hbRot]
    exact hrotSnd.symm
  have hab' : G.Adj P.snd D.snd := by simpa [haEq, hbEq] using hab
  have hBmem : D.snd ∈ D.support.tail := D.snd_mem_tail_support hDnotNil
  have hBnotA : D.snd ∉ A.support := by
    intro hbA
    have hbP : D.snd ∈ P.support.tail := by
      simpa [A, P.support_tail_of_not_nil hPnotNil] using hbA
    exact hdisjPD hbP hBmem
  let R : G.Walk y D.snd := A.reverse.concat hab'
  have hRPath : R.IsPath := hAPath.reverse.concat (by
    simpa using hBnotA) hab'
  let q : G.Walk y x := R.append B
  have hdisjAB : A.support.reverse.Disjoint B.support := by
    rw [List.disjoint_left]
    intro z hzA hzB
    apply hdisjPD
    · have hzA' : z ∈ A.support := by simpa using hzA
      simpa [A, P.support_tail_of_not_nil hPnotNil] using hzA'
    · simpa [B, D.support_tail_of_not_nil hDnotNil] using hzB
  have hqSupport : q.support = A.support.reverse ++ B.support := by
    calc
      q.support = R.support ++ B.support.tail := by
        exact SimpleGraph.Walk.support_append R B
      _ = (A.reverse.support ++ [D.snd]) ++ B.support.tail := by
        rw [show R = A.reverse.concat hab' by rfl,
          SimpleGraph.Walk.support_concat]
      _ = A.support.reverse ++ (D.snd :: B.support.tail) := by
        simp only [SimpleGraph.Walk.support_reverse]
        simp
      _ = A.support.reverse ++ B.support := by
        rw [B.cons_tail_support]
  have hqPath : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hqSupport,
      List.nodup_append]
    refine ⟨(List.nodup_reverse.mpr hAPath.support_nodup),
      hBPath.support_nodup, ?_⟩
    intro a ha b hb
    intro heq
    subst b
    exact hdisjAB ha hb
  refine ⟨q, hqPath, ?_, ?_⟩
  · have hlenPD := congrArg SimpleGraph.Walk.length hPD
    have hPlen : P.length = A.length + 1 := by
      have := P.length_tail_add_one hPnotNil
      simpa [A] using this.symm
    have hDlen : D.length = B.length + 1 := by
      have := D.length_tail_add_one hDnotNil
      simpa [B] using this.symm
    simp only [SimpleGraph.Walk.length_append] at hlenPD
    simp [q, R, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_concat]
    change A.length + 1 + B.length = C.length - 1
    have hrlen : r.length = C.length := by
      simpa [r, CycleWitness.length] using
        C.walk.length_rotate x hxS
    omega
  · intro z hzq
    have hzR : z ∈ r.support := by
      rw [hqSupport] at hzq
      simp only [List.mem_append, List.mem_reverse] at hzq
      rcases hzq with hzA | hzB
      · have hzP : z ∈ P.support := by
          exact List.mem_of_mem_tail (by
            simpa [A, P.support_tail_of_not_nil hPnotNil] using hzA)
        exact r.support_takeUntil_subset_support hyR hzP
      · have hzD : z ∈ D.support := by
          apply List.mem_of_mem_tail
          rw [← D.support_tail_of_not_nil hDnotNil]
          simpa [B] using hzB
        exact r.support_dropUntil_subset_support hyR hzD
    have hzC : z ∈ C.walk.support :=
      (C.walk.mem_support_rotate_iff x hxS).mp hzR
    simpa [CycleWitness.vertexFinset] using hzC

/-- The forward successors of two attachment vertices joined by an external
two-edge path cannot themselves be adjacent.  This is the cycle-splicing
argument used in the zero-longest-path branch of Ma--Ning edge Lemma (i). -/
theorem not_adj_cycleSuccessors_of_external_two_path
    (C : CycleWitness G) (hloc : IsLocallyMaximalCycle C)
    {x y : V} (hx : x ∈ C.vertexFinset) (hy : y ∈ C.vertexFinset)
    (hxy : x ≠ y) (p : G.Walk x y) (hp : p.IsPath)
    (hplen : p.length = 2)
    (hpout : p.support.toFinset \ {x, y} ⊆
      Finset.univ \ C.vertexFinset) :
    ¬ G.Adj (cycleSuccessor C x) (cycleSuccessor C y) := by
  classical
  intro hadj
  have hax := cycleSuccessor_ne_of_external_two_path
    C hloc hx hy hxy p hp hplen hpout
  have hpRevOut : p.reverse.support.toFinset \ {y, x} ⊆
      Finset.univ \ C.vertexFinset := by
    intro z hz
    apply hpout
    simpa [SimpleGraph.Walk.support_reverse, Finset.pair_comm] using hz
  have hby := cycleSuccessor_ne_of_external_two_path
    C hloc hy hx hxy.symm p.reverse hp.reverse (by simpa using hplen)
      hpRevOut
  obtain ⟨q, hqPath, hqLen, hqSupport⟩ :=
    exists_successor_chord_complement_path C hx hy hxy hax hby hadj
  have hxNotTail : x ∉ p.support.tail := by
    have hnodup : (x :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hyNotQTail : y ∉ q.support.tail := by
    have hnodup : (y :: q.support.tail).Nodup := by
      rw [q.cons_tail_support]
      exact hqPath.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisj : p.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzq
    have hzC : z ∈ C.vertexFinset :=
      hqSupport z (List.mem_of_mem_tail hzq)
    have hzx : z ≠ x := by
      intro hzx
      subst z
      exact hxNotTail hzp
    have hzy : z ≠ y := by
      intro hzy
      subst z
      exact hyNotQTail hzq
    have hzInt : z ∈ p.support.toFinset \ {x, y} := by
      apply Finset.mem_sdiff.mpr
      exact ⟨by simpa using List.mem_of_mem_tail hzp,
        by simp [hzx, hzy]⟩
    exact (Finset.mem_sdiff.mp (hpout hzInt)).2 hzC
  let Dwalk : G.Walk x x := p.append q
  have hDcycle : Dwalk.IsCycle :=
    hp.isCycle_append hqPath hdisj (Or.inl (by omega))
  let D : CycleWitness G := ⟨x, Dwalk, hDcycle⟩
  have hDlong : C.length < D.length := by
    change C.length < (p.append q).length
    rw [SimpleGraph.Walk.length_append, hplen, hqLen]
    omega
  have hcrossSub : cycleCrossingEdges C D ⊆
      {s(x, p.snd), s(y, p.penultimate)} := by
    intro e heCross
    have heD := (Finset.mem_inter.mp heCross).1
    have heAcross := (Finset.mem_inter.mp heCross).2
    have heList : e ∈ Dwalk.edges := by
      simpa [D, CycleWitness.edgeFinset] using heD
    rw [SimpleGraph.Walk.edges_append] at heList
    have heCases : e ∈ p.edges ∨ e ∈ q.edges := by simpa using heList
    unfold edgesBetween at heAcross
    obtain ⟨heG, a, haC, b, hbOut, hab⟩ :=
      Finset.mem_filter.mp heAcross
    rcases heCases with hep | heq
    · rw [hab] at hep
      have haSupport : a ∈ p.support :=
        p.fst_mem_support_of_mem_edges hep
      have haEnds : a = x ∨ a = y := by
        by_contra hEnds
        push Not at hEnds
        have haInt : a ∈ p.support.toFinset \ {x, y} := by
          apply Finset.mem_sdiff.mpr
          exact ⟨by simpa using haSupport,
            by simp [hEnds.1, hEnds.2]⟩
        exact (Finset.mem_sdiff.mp (hpout haInt)).2 haC
      rcases haEnds with rfl | rfl
      · have hbEq : b = p.snd := hp.eq_snd_of_mem_edges hep
        simp [hab, hbEq]
      · have hbEq : b = p.penultimate :=
          hp.eq_penultimate_of_mem_edges hep
        simp [hab, hbEq]
    · rw [hab] at heq
      have hbSupport : b ∈ q.support :=
        q.snd_mem_support_of_mem_edges heq
      exact ((Finset.mem_sdiff.mp hbOut).2
        (hqSupport b hbSupport)).elim
  have hcrossUpper : (cycleCrossingEdges C D).card ≤ 2 :=
    (Finset.card_le_card hcrossSub).trans Finset.card_le_two
  have hcrossLower := hloc D hDlong
  omega

def componentSuccessorSet (C : CycleWitness G)
    (c : (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    Finset V :=
  (setNeighborsIn G (componentOutsideFinset C c) C.vertexFinset).image
    (cycleSuccessor C)

theorem componentSuccessorSet_card (C : CycleWitness G)
    (c : (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    (componentSuccessorSet C c).card = componentAttachmentCount C c := by
  classical
  rw [componentSuccessorSet, Finset.card_image_iff.mpr]
  · rfl
  · exact (cycleSuccessor C).injective.injOn

theorem componentSuccessorSet_subset_cycle (C : CycleWitness G)
    (c : (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    componentSuccessorSet C c ⊆ C.vertexFinset := by
  classical
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  exact cycleSuccessor_mem C (Finset.mem_filter.mp hx).1

/-- If the selected terminal component has longest-path length zero, the
successors of all its cycle attachments form an independent set. -/
theorem componentSuccessorSet_isIndep_of_length_zero
    (C : CycleWitness G) (hloc : IsLocallyMaximalCycle C)
    (hterminal : IsSwitchingTerminal G C)
    (c : (G.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (hell : componentLongestPathLength C c = 0) :
    G.IsIndepSet (↑(componentSuccessorSet C c) : Set V) := by
  classical
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab
  obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact hab (hxa.symm.trans hyb)
  obtain ⟨p, hp, hplen, hpQ⟩ :=
    exists_terminal_component_path C hterminal c x y hx hy hxy
  have hpout : p.support.toFinset \ {x, y} ⊆
      Finset.univ \ C.vertexFinset := fun _ hz =>
    (componentOutsideFinset_isComponent C c).2.1 (hpQ hz)
  subst a
  subst b
  apply not_adj_cycleSuccessors_of_external_two_path
    C hloc (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      hxy p hp
  · omega
  · exact hpout

/-- A cycle-independent set has at most `s` vertices when deleting `s-1`
cycle vertices leaves a clique. -/
theorem indep_card_le_of_cycle_sdiff_clique
    (C : CycleWitness G) (U S : Finset V) (s : ℕ)
    (hUsub : U ⊆ C.vertexFinset)
    (hUindep : G.IsIndepSet (↑U : Set V))
    (hSsub : S ⊆ C.vertexFinset) (hScard : S.card = s - 1)
    (hclique : G.IsClique (↑(C.vertexFinset \ S) : Set V))
    (hs2 : 2 ≤ s) :
    U.card ≤ s := by
  classical
  have hsmall : (U \ S).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have haU := (Finset.mem_sdiff.mp ha).1
    have hbU := (Finset.mem_sdiff.mp hb).1
    have haA : a ∈ C.vertexFinset \ S :=
      Finset.mem_sdiff.mpr ⟨hUsub haU, (Finset.mem_sdiff.mp ha).2⟩
    have hbA : b ∈ C.vertexFinset \ S :=
      Finset.mem_sdiff.mpr ⟨hUsub hbU, (Finset.mem_sdiff.mp hb).2⟩
    have hadj := (SimpleGraph.isClique_iff G).mp hclique haA hbA hab
    exact (SimpleGraph.isIndepSet_iff G).mp hUindep haU hbU hab hadj
  have hinter : (U ∩ S).card ≤ S.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit := Finset.card_sdiff_add_card_inter U S
  omega

end
end Erdos767

