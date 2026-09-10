import Erdos767.CycleCaseBounds

/-!
# Edge decomposition across an arbitrary finite vertex set
-/

open scoped Sym2

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

/-- Every edge lies inside `A`, inside its complement, or crosses between
the two. -/
theorem edge_count_finset_decomposition
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    G.edgeFinset.card =
      (G.induce (↑A : Set V)).edgeFinset.card +
      ((G.induce (↑(Finset.univ \ A) : Set V)).edgeFinset.card +
        (edgesBetween G (Finset.univ \ A) A).card) := by
  classical
  let I : Finset (Sym2 V) :=
    {e ∈ G.edgeFinset | e.toFinset ⊆ A}
  let O : Finset (Sym2 V) :=
    {e ∈ G.edgeFinset | e.toFinset ⊆ Finset.univ \ A}
  let B : Finset (Sym2 V) :=
    edgesBetween G (Finset.univ \ A) A
  have hpart : G.edgeFinset = I ∪ O ∪ B := by
    ext e
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
          by_cases hxA : x ∈ A
          · by_cases hyA : y ∈ A
            · apply Finset.mem_union_left
              apply Finset.mem_union_left
              apply Finset.mem_filter.mpr
              refine ⟨he, ?_⟩
              intro z hz
              have hz' : z = x ∨ z = y := by simpa using hz
              exact hz'.elim (fun h ↦ h ▸ hxA) (fun h ↦ h ▸ hyA)
            · apply Finset.mem_union_right
              unfold B edgesBetween
              apply Finset.mem_filter.mpr
              refine ⟨he, y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyA⟩,
                x, hxA, Sym2.eq_swap⟩
          · by_cases hyA : y ∈ A
            · apply Finset.mem_union_right
              unfold B edgesBetween
              apply Finset.mem_filter.mpr
              exact ⟨he, x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxA⟩,
                y, hyA, rfl⟩
            · apply Finset.mem_union_left
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨he, ?_⟩
              intro z hz
              have hz' : z = x ∨ z = y := by simpa using hz
              exact hz'.elim
                (fun h ↦ h ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxA⟩)
                (fun h ↦ h ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyA⟩)
    · intro he
      rcases Finset.mem_union.mp he with heIO | heB
      · rcases Finset.mem_union.mp heIO with heI | heO
        · exact (Finset.mem_filter.mp heI).1
        · exact (Finset.mem_filter.mp heO).1
      · exact (Finset.mem_filter.mp heB).1
  have hIO : Disjoint I O := by
    apply Finset.disjoint_left.mpr
    intro e heI heO
    have hI := (Finset.mem_filter.mp heI).2
    have hO := (Finset.mem_filter.mp heO).2
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxmem : x ∈ s(x, y).toFinset := by simp
        exact (Finset.mem_sdiff.mp (hO hxmem)).2 (hI hxmem)
  have hIB : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro e heI heB
    have hI := (Finset.mem_filter.mp heI).2
    unfold B edgesBetween at heB
    obtain ⟨_, x, hxO, y, hyA, hxy⟩ := Finset.mem_filter.mp heB
    have hxA : x ∈ A := by
      apply hI
      rw [hxy]
      simp
    exact (Finset.mem_sdiff.mp hxO).2 hxA
  have hOB : Disjoint O B := by
    apply Finset.disjoint_left.mpr
    intro e heO heB
    have hO := (Finset.mem_filter.mp heO).2
    unfold B edgesBetween at heB
    obtain ⟨_, x, hxO, y, hyA, hxy⟩ := Finset.mem_filter.mp heB
    have hyO : y ∈ Finset.univ \ A := by
      apply hO
      rw [hxy]
      simp
    exact (Finset.mem_sdiff.mp hyO).2 hyA
  have hIOB : Disjoint (I ∪ O) B :=
    Finset.disjoint_union_left.mpr ⟨hIB, hOB⟩
  rw [hpart, Finset.card_union_of_disjoint hIOB,
    Finset.card_union_of_disjoint hIO]
  unfold I O B
  rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset,
    SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  omega

end

end Erdos767
