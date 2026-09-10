import Erdos767.ExceptionalCertificate

/-!
# The exceptional `(k,n,c) = (3,8,6)` case

The graph is first labelled so that a longest six-cycle is `0,…,5`.
The labelled graph is then passed to the manuscript-faithful combinatorial
classification in `ExceptionalCertificate`.
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

theorem cycleWitness_of_graphHasCycleEmbedding
    (K : SimpleGraph (Fin 8)) [DecidableRel K.Adj]
    {m : ℕ} [NeZero m] (hm3 : 3 ≤ m) (h : GraphHasCycleEmbedding K m) :
    ∃ D : CycleWitness K, D.length = m := by
  rcases h with ⟨f, hf⟩
  let φ : cycleGraph m →g K :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        rw [cycleGraph_adj'] at hxy
        rcases hxy with hxy | hyx
        · have hy : nextFin m y = x := by
            have heq : x - y = (1 : Fin m) := by
              apply Fin.ext
              simpa [Nat.mod_eq_of_lt (by omega : 1 < m)] using hxy
            have hxy' : x = y + 1 := (sub_eq_iff_eq_add').mp heq
            apply Fin.ext
            simpa [nextFin, Fin.val_add,
              Nat.mod_eq_of_lt (by omega : 1 < m)] using
                congrArg Fin.val hxy'.symm
          rw [← hy]
          exact (hf y).symm
        · have hx : nextFin m x = y := by
            have heq : y - x = (1 : Fin m) := by
              apply Fin.ext
              simpa [Nat.mod_eq_of_lt (by omega : 1 < m)] using hyx
            have hyx' : y = x + 1 := (sub_eq_iff_eq_add').mp heq
            apply Fin.ext
            simpa [nextFin, Fin.val_add,
              Nat.mod_eq_of_lt (by omega : 1 < m)] using
                congrArg Fin.val hyx'.symm
          rw [← hx]
          exact hf x }
  have hcontained : cycleGraph m ⊑ K := ⟨⟨φ, f.injective⟩⟩
  obtain ⟨v, p, hpcycle, hplen⟩ :=
    (cycleGraph_isContained_iff (by omega : 2 < m)).mp hcontained
  exact ⟨⟨v, p, hpcycle⟩, hplen⟩

/-- Label the six vertices of a length-six cycle in cyclic order by
`0,…,5`, and label the two remaining vertices by `6,7`. -/
theorem exists_ordered_cycle_labeling
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V = 8) (C : CycleWitness G)
    (hlen : C.length = 6) :
    ∃ e : Fin 8 ≃ V,
      (∀ i : Fin 6, e ⟨i.1, by omega⟩ = C.walk.getVert i.1) ∧
      sixSet.map e.toEmbedding = C.vertexFinset := by
  classical
  let L := C.walk.support.dropLast
  let O := Finset.univ \ L.toFinset
  let E := L ++ O.toList
  have hLn : L.Nodup := C.isCycle.nodup_dropLast_support
  have hLE : L.toFinset = C.vertexFinset := by
    simpa [L] using C.dropLast_support_toFinset
  have hLlen : L.length = 6 := by
    dsimp [L]
    rw [List.length_dropLast, C.walk.length_support]
    simpa [CycleWitness.length] using hlen
  have hOcard : O.card = 2 := by
    dsimp [O]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, List.toFinset_card_of_nodup hLn, hLlen, hcard]
  have hEn : E.Nodup := by
    dsimp [E]
    rw [List.nodup_append]
    refine ⟨hLn, O.nodup_toList, ?_⟩
    intro x hxL y hyO hxy
    subst y
    have hxLf : x ∈ L.toFinset := by simpa using hxL
    have hxOf : x ∈ O := by simpa using hyO
    exact (Finset.mem_sdiff.mp hxOf).2 hxLf
  have hElen : E.length = 8 := by
    simp [E, hLlen, hOcard]
  have hEall : ∀ x : V, x ∈ E := by
    intro x
    dsimp [E]
    by_cases hx : x ∈ L.toFinset
    · apply List.mem_append_left
      simpa using hx
    · apply List.mem_append_right
      simpa [O, hx]
  let e0 : Fin E.length ≃ V := hEn.getEquivOfForallMemList E hEall
  let e : Fin 8 ≃ V := (finCongr hElen.symm).trans e0
  have e_apply (i : Fin 8) : e i = E[i.1] := by
    simp [e, e0, List.Nodup.getEquivOfForallMemList]
  refine ⟨e, ?_, ?_⟩
  · intro i
    rw [e_apply]
    rw [show E[i.1] = L[i.1] by
      simp [E, List.getElem_append_left, hLlen, i.2]]
    simp [L, List.getElem_dropLast, C.walk.support_getElem_eq_getVert]
  · apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hi6 : i.1 < 6 := by simpa [sixSet] using hi
      have heq : e i = C.walk.getVert i.1 := by
        rw [e_apply]
        rw [show E[i.1] = L[i.1] by
          simp [E, List.getElem_append_left, hLlen, hi6]]
        simp [L, List.getElem_dropLast,
          C.walk.support_getElem_eq_getVert]
      change e i ∈ C.vertexFinset
      rw [heq]
      simpa [CycleWitness.vertexFinset] using C.walk.getVert_mem_support i.1
    · intro x hx
      have hxL : x ∈ L := by
        rw [← hLE] at hx
        simpa using hx
      obtain ⟨i, hix⟩ := List.get_of_mem hxL
      have hi6 : i.1 < 6 := by rw [← hLlen]; exact i.2
      let j : Fin 8 := ⟨i.1, by omega⟩
      apply Finset.mem_map.mpr
      refine ⟨j, ?_, ?_⟩
      · simp [sixSet, j, hi6]
      · change e j = x
        rw [e_apply]
        rw [show E[i.1] = L[i.1] by
          simp [E, List.getElem_append_left, hLlen, hi6]]
        exact hix

/-- The exceptional numerical configuration from the proof of
`lem:base` cannot occur.  This is the invariant, arbitrarily labelled graph
interface to `exceptional_fin8_impossible_paper`: the proof first labels the
six-cycle by `0,...,5`, transports the whole graph to `Fin 8`, and then
invokes the step-by-step combinatorial proof above. -/
theorem exceptional_case_contradiction
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 8)
    (C : CycleWitness G) (hlen : C.length = 6)
    (hlongest : IsLongestCycle C)
    (hedges : G.edgeFinset.card = 17)
    (hinside :
      (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card = 11)
    (hmindegree : ∀ x : V, 3 ≤ G.degree x)
    (hcycleDegree : ∀ (x : V) (hx : x ∈ C.vertexFinset),
      (G.induce (↑C.vertexFinset : Set V)).degree ⟨x, hx⟩ ≤ 4) :
    False := by
  classical
  obtain ⟨e, horder, hmap⟩ := exists_ordered_cycle_labeling hcard C hlen
  let K : SimpleGraph (Fin 8) := G.comap e
  let ι : K ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel K.Adj := Classical.decRel _
  have himage : e '' (↑sixSet : Set (Fin 8)) =
      (↑C.vertexFinset : Set V) := by
    ext x
    rw [← hmap]
    simp
  have hbij : Set.BijOn e (↑sixSet : Set (Fin 8))
      (↑C.vertexFinset : Set V) := by
    rw [← himage]
    exact e.injective.bijOn_image
  let ιC : K.induce (↑sixSet : Set (Fin 8)) ≃g
      G.induce (↑C.vertexFinset : Set V) := ι.induce hbij
  have he0 : e (0 : Fin 8) = C.walk.getVert 0 := by simpa using horder 0
  have he1 : e (1 : Fin 8) = C.walk.getVert 1 := by simpa using horder 1
  have he2 : e (2 : Fin 8) = C.walk.getVert 2 := by simpa using horder 2
  have he3 : e (3 : Fin 8) = C.walk.getVert 3 := by simpa using horder 3
  have he4 : e (4 : Fin 8) = C.walk.getVert 4 := by simpa using horder 4
  have he5 : e (5 : Fin 8) = C.walk.getVert 5 := by simpa using horder 5
  have hcanonical :
      K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧
      K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0 := by
    have hadj (i : Fin 6) :
        G.Adj (C.walk.getVert i.1) (C.walk.getVert (i.1 + 1)) := by
      apply C.walk.adj_getVert_succ
      change i.1 < C.length
      omega
    constructor
    · change G.Adj (e 0) (e 1)
      rw [he0, he1]
      exact hadj 0
    constructor
    · change G.Adj (e 1) (e 2)
      rw [he1, he2]
      exact hadj 1
    constructor
    · change G.Adj (e 2) (e 3)
      rw [he2, he3]
      exact hadj 2
    constructor
    · change G.Adj (e 3) (e 4)
      rw [he3, he4]
      exact hadj 3
    constructor
    · change G.Adj (e 4) (e 5)
      rw [he4, he5]
      exact hadj 4
    · change G.Adj (e 5) (e 0)
      rw [he5, he0]
      have hwlen : C.walk.length = 6 := by
        simpa [CycleWitness.length] using hlen
      have hlast : C.walk.getVert 6 = C.base := by
        simpa [hwlen] using C.walk.getVert_length
      simpa [hlast] using hadj 5
  have hedgesK : K.edgeFinset.card = 17 := by
    calc
      K.edgeFinset.card = G.edgeFinset.card := ι.card_edgeFinset_eq
      _ = 17 := hedges
  have hinsideK :
      (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card = 11 := by
    calc
      (K.induce (↑sixSet : Set (Fin 8))).edgeFinset.card =
          (G.induce (↑C.vertexFinset : Set V)).edgeFinset.card :=
        ιC.card_edgeFinset_eq
      _ = 11 := hinside
  have hminK : ∀ x : Fin 8, 3 ≤ K.degree x := by
    intro x
    rw [← ι.degree_eq x]
    exact hmindegree (e x)
  have hcycleK : ∀ x ∈ sixSet,
      (sixSet.filter fun y ↦ K.Adj x y).card ≤ 4 := by
    intro x hx
    rw [← induce_six_degree_eq_filter_card K x hx]
    rw [← ιC.degree_eq ⟨x, hx⟩]
    exact hcycleDegree (e x) (hbij.mapsTo hx)
  have noLongEmbedding (m : ℕ) [NeZero m] (hm3 : 3 ≤ m)
      (hm6 : 6 < m) : ¬ GraphHasCycleEmbedding K m := by
    intro hemb
    obtain ⟨D, hDlen⟩ := cycleWitness_of_graphHasCycleEmbedding K hm3 hemb
    let p : G.Walk (ι D.base) (ι D.base) := D.walk.map ι.toHom
    have hpcycle : p.IsCycle := by
      exact (SimpleGraph.Walk.isCycle_map_iff_of_injective ι.injective).2 D.isCycle
    let E : CycleWitness G := ⟨ι D.base, p, hpcycle⟩
    have hElen : E.length = m := by
      simpa [E, p, CycleWitness.length] using hDlen
    have hle := hlongest E
    rw [hElen, hlen] at hle
    omega
  exact exceptional_fin8_impossible_paper K hcanonical hedgesK hinsideK hminK
    hcycleK (noLongEmbedding 7 (by omega) (by omega))
    (noLongEmbedding 8 (by omega) (by omega))

end

end Erdos767

