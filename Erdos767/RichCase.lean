import Erdos767.FinsetEdgeDecomposition

/-!
# The exterior-rich Ma--Ning case
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

local instance richCaseDecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

/-- Moving more of a fixed degree budget from internal edges to crossing
edges can only increase `x + floor ((A-x)/2)`. -/
theorem half_budget_mono {A x y : ℕ} (hxy : x ≤ y) (hyA : y ≤ A) :
    x + (A - x) / 2 ≤ y + (A - y) / 2 := by
  omega

/-- Pure arithmetic at the end of the rich-host argument. -/
theorem rich_host_arithmetic
    {k n c q tau e eS eSX : ℕ}
    (hq : q = c / 2) (htau : tau = c - 2 * q + 1)
    (htau1 : 1 ≤ tau) (htau2 : tau ≤ 2)
    (hcn : c < n)
    (hqA : q ∈ A k)
    (hedge : e ≤ eSX + eS + q * (n - c) + tau - 1)
    (hdegree : 2 * eS + eSX ≤ q * (k + 1))
    (hcross : eSX ≤ q * (c - q)) :
    e ≤ p k n := by
  have hqBounds := mem_A_iff.mp hqA
  have hq1 : 1 ≤ q := by omega
  have hpLower := p_ge_splitTerm (n := n) hqA
  by_cases hXsmall : c - q ≤ k + 1
  · have hBA : q * (c - q) ≤ q * (k + 1) :=
      Nat.mul_le_mul_left q hXsmall
    have heSA : eS ≤ (q * (k + 1) - eSX) / 2 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
      omega
    have hmono := half_budget_mono hcross hBA
    have hpre : e ≤
        q * (c - q) + (q * (k + 1) - q * (c - q)) / 2 +
          q * (n - c) + tau - 1 := by
      calc
        e ≤ eSX + eS + q * (n - c) + tau - 1 := hedge
        _ ≤ (eSX + (q * (k + 1) - eSX) / 2) +
              q * (n - c) + tau - 1 := by omega
        _ ≤ (q * (c - q) +
              (q * (k + 1) - q * (c - q)) / 2) +
              q * (n - c) + tau - 1 := by omega
    have htauCases : tau = 1 ∨ tau = 2 := by omega
    rcases htauCases with rfl | rfl
    · have hcEq : c = 2 * q := by omega
      have hqcn : q ≤ c := by omega
      have hqkn : q ≤ k + 1 := hqBounds.2
      have htarget :
          q * (c - q) + (q * (k + 1) - q * (c - q)) / 2 +
              q * (n - c) + 1 - 1 = splitTerm k n q := by
        have hcsub : 2 * q - q = q := by omega
        have hAsub : q * (k + 1) - q * q = q * (k + 1 - q) := by
          exact (Nat.mul_sub_left_distrib q (k + 1) q).symm
        have hmain : q * q + q * (n - 2 * q) = q * (n - q) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        unfold splitTerm
        rw [hcEq, hcsub, hAsub]
        omega
      rw [htarget] at hpre
      exact hpre.trans hpLower
    · have hcEq : c = 2 * q + 1 := by omega
      have hqk : q ≤ k := by omega
      have hAsub : q * (k + 1) - q * (c - q) = q * (k - q) := by
        rw [hcEq]
        have hcsub : 2 * q + 1 - q = q + 1 := by omega
        rw [hcsub]
        have hleft : q * (k + 1) - q * (q + 1) =
            q * ((k + 1) - (q + 1)) :=
          (Nat.mul_sub_left_distrib q (k + 1) (q + 1)).symm
        rw [hleft]
        congr 1
        omega
      rw [hAsub] at hpre
      have hfloor : (q * (k - q)) / 2 + 1 ≤
          (q * (k + 1 - q)) / 2 := by
        have hrewrite : q * (k + 1 - q) = q * (k - q) + q := by
          have hsub : k + 1 - q = (k - q) + 1 := by omega
          rw [hsub, Nat.mul_add, Nat.mul_one]
        rw [hrewrite]
        omega
      have hsplit :
          q * (c - q) + (q * (k - q)) / 2 +
              q * (n - c) + 2 - 1 ≤ splitTerm k n q := by
        have hcsub : 2 * q + 1 - q = q + 1 := by omega
        have hmain : q * (q + 1) + q * (n - (2 * q + 1)) =
            q * (n - q) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        unfold splitTerm
        rw [hcEq, hcsub]
        calc
          q * (q + 1) + q * (k - q) / 2 +
                q * (n - (2 * q + 1)) + 2 - 1 =
              q * (n - q) + (q * (k - q) / 2 + 1) := by omega
          _ ≤ q * (n - q) + q * (k + 1 - q) / 2 :=
            Nat.add_le_add_left hfloor _
      exact hpre.trans (hsplit.trans hpLower)
  · have hXlarge : k + 2 ≤ c - q := by omega
    have htauEq : tau = 2 := by
      by_contra hne
      have htauEq1 : tau = 1 := by omega
      have hcEq : c = 2 * q := by omega
      omega
    have hcEq : c = 2 * q + 1 := by omega
    have hqEq : q = k + 1 := by
      have hqUpper := hqBounds.2
      omega
    have hesum : eS + eSX ≤ q * q := by
      rw [hqEq] at hdegree
      nlinarith
    have hpre : e ≤ q * q + q * (n - c) + 1 := by
      rw [htauEq] at hedge
      omega
    have hterminal : q * q + q * (n - c) + 1 ≤ q * (n - q) := by
      have hmain : q * q + q * (n - c) = q * (n - q - 1) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      rw [hmain]
      have hstep : q * (n - q - 1) + q = q * (n - q) := by
        have hnq : 1 ≤ n - q := by omega
        have hsub : n - q - 1 + 1 = n - q := by omega
        calc
          q * (n - q - 1) + q = q * (n - q - 1) + q * 1 := by
            rw [Nat.mul_one]
          _ = q * (n - q - 1 + 1) := (Nat.mul_add _ _ _).symm
          _ = q * (n - q) := by rw [hsub]
      omega
    have hsplit : q * (n - q) ≤ splitTerm k n q := by
      simp [splitTerm, hqEq]
    exact hpre.trans (hterminal.trans (hsplit.trans hpLower))

/-- Degree sum over a vertex subset: internal edges are counted twice and
crossing edges once. -/
theorem sum_degrees_finset_eq_twice_inside_add_crossing
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ x ∈ S, G.degree x) =
      2 * (G.induce (↑S : Set V)).edgeFinset.card +
        (edgesBetween G S (Finset.univ \ S)).card := by
  classical
  let T := Finset.univ \ S
  have hST : Disjoint S T := by
    exact Finset.disjoint_sdiff
  have hdegreeSplit : ∀ x ∈ S,
      G.degree x =
        (neighborsIn G x S).card + (neighborsIn G x T).card := by
    intro x hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hneigh : G.neighborFinset x =
        neighborsIn G x S ∪ neighborsIn G x T := by
      ext y
      simp only [SimpleGraph.mem_neighborFinset, neighborsIn,
        Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      constructor
      · intro hxy
        by_cases hyS : y ∈ S
        · exact Or.inl ⟨hyS, hxy⟩
        · have hyT : y ∈ T := Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ _, hyS⟩
          exact Or.inr ⟨hyT, hxy⟩
      · rintro (⟨_, hxy⟩ | ⟨_, hxy⟩) <;> exact hxy
    rw [hneigh, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro y hyS hyT
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyT).1).2
      (Finset.mem_filter.mp hyS).1
  have hinside : (∑ x ∈ S, (neighborsIn G x S).card) =
      2 * (G.induce (↑S : Set V)).edgeFinset.card := by
    have hhand := (G.induce (↑S : Set V)).sum_degrees_eq_twice_card_edges
    rw [← hhand]
    rw [Finset.sum_subtype S (by intro x; rfl)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hmap :
        ((G.induce (↑S : Set V)).neighborFinset x).map
            (Function.Embedding.subtype (· ∈ S)) =
          neighborsIn G (x : V) S := by
      ext y
      simp [neighborsIn, and_comm]
    have := congrArg Finset.card hmap
    simpa using this.symm
  have hcross : (∑ x ∈ S, (neighborsIn G x T).card) =
      (edgesBetween G S T).card := by
    exact (edgesBetween_card_eq_sum_neighborsIn S T hST).symm
  calc
    (∑ x ∈ S, G.degree x) =
        (∑ x ∈ S, ((neighborsIn G x S).card +
          (neighborsIn G x T).card)) := by
      apply Finset.sum_congr rfl
      exact hdegreeSplit
    _ = (∑ x ∈ S, (neighborsIn G x S).card) +
          (∑ x ∈ S, (neighborsIn G x T).card) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (G.induce (↑S : Set V)).edgeFinset.card +
          (edgesBetween G S (Finset.univ \ S)).card := by
      rw [hinside, hcross]

/-- The cycle-degree lemma summed only over `S`, with the cycle split as
`S ∪ (V(C) \ S)`. -/
theorem cycle_partition_degree_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G) (S : Finset V)
    (hSsub : S ⊆ C.vertexFinset) :
    2 * (G.induce (↑S : Set V)).edgeFinset.card +
        (edgesBetween G S (C.vertexFinset \ S)).card ≤
      S.card * (k + 1) := by
  classical
  let X := C.vertexFinset \ S
  have hSX : Disjoint S X := Finset.disjoint_sdiff
  have hCpart : S ∪ X = C.vertexFinset :=
    Finset.union_sdiff_of_subset hSsub
  have hdegreeSplit : ∀ (s : V) (hs : s ∈ S),
      (G.induce (↑C.vertexFinset : Set V)).degree ⟨s, hSsub hs⟩ =
        (neighborsIn G s S).card + (neighborsIn G s X).card := by
    intro s hs
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hmap :
        ((G.induce (↑C.vertexFinset : Set V)).neighborFinset
          ⟨s, hSsub hs⟩).map
            (Function.Embedding.subtype (· ∈ C.vertexFinset)) =
          neighborsIn G s S ∪ neighborsIn G s X := by
      ext y
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset,
        SimpleGraph.induce_adj, Function.Embedding.coe_subtype,
        neighborsIn, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨z, hzs, rfl⟩
        have hzPart : (z : V) ∈ S ∨ (z : V) ∈ X := by
          by_cases hzS : (z : V) ∈ S
          · exact Or.inl hzS
          · exact Or.inr (Finset.mem_sdiff.mpr ⟨z.property, hzS⟩)
        exact hzPart.elim (fun hzS ↦ Or.inl ⟨hzS, hzs⟩)
          (fun hzX ↦ Or.inr ⟨hzX, hzs⟩)
      · rintro (⟨hyS, hsy⟩ | ⟨hyX, hsy⟩)
        · exact ⟨⟨y, hSsub hyS⟩, hsy, rfl⟩
        · exact ⟨⟨y, (Finset.mem_sdiff.mp hyX).1⟩, hsy, rfl⟩
    have hcardMap := congrArg Finset.card hmap
    rw [Finset.card_map, Finset.card_union_of_disjoint] at hcardMap
    · exact hcardMap
    · apply Finset.disjoint_left.mpr
      intro y hyS hyX
      exact (Finset.disjoint_left.mp hSX
        (Finset.mem_filter.mp hyS).1 (Finset.mem_filter.mp hyX).1)
  have hinside : (∑ s ∈ S, (neighborsIn G s S).card) =
      2 * (G.induce (↑S : Set V)).edgeFinset.card := by
    have hhand := (G.induce (↑S : Set V)).sum_degrees_eq_twice_card_edges
    rw [← hhand, Finset.sum_subtype S (by intro x; rfl)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hmap :
        ((G.induce (↑S : Set V)).neighborFinset s).map
            (Function.Embedding.subtype (· ∈ S)) =
          neighborsIn G (s : V) S := by
      ext y
      simp [neighborsIn, and_comm]
    have hcardMap := congrArg Finset.card hmap
    simpa using hcardMap.symm
  have hcross : (∑ s ∈ S, (neighborsIn G s X).card) =
      (edgesBetween G S X).card :=
    (edgesBetween_card_eq_sum_neighborsIn S X hSX).symm
  have hpoint : ∀ s ∈ S,
      (neighborsIn G s S).card + (neighborsIn G s X).card ≤ k + 1 := by
    intro s hs
    rw [← hdegreeSplit s hs]
    exact cycle_degree_on_cycle hfree C s (hSsub hs)
  have hsumBound :
      (∑ s ∈ S, ((neighborsIn G s S).card +
        (neighborsIn G s X).card)) ≤ S.card * (k + 1) := by
    simpa [Nat.mul_comm] using S.sum_le_card_nsmul
      (fun s ↦ (neighborsIn G s S).card + (neighborsIn G s X).card)
      (k + 1) hpoint
  rw [Finset.sum_add_distrib, hinside, hcross] at hsumBound
  exact hsumBound

set_option maxHeartbeats 3000000 in
/-- All graph-theoretic bookkeeping for a graph contained in the rich
`W_(n,q,c)` host. -/
theorem rich_host_accounting
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k n : ℕ} (hcard : Fintype.card V = n)
    (hfree : PathFanFree G (k + 2)) (C : CycleWitness G)
    (hW : IsSubgraphOfW G n (C.length / 2) C.length) :
    ∃ eS eSX tau : ℕ,
      tau = C.length - 2 * (C.length / 2) + 1 ∧
      1 ≤ tau ∧ tau ≤ 2 ∧
      G.edgeFinset.card ≤
        eSX + eS + (C.length / 2) * (n - C.length) + tau - 1 ∧
      2 * eS + eSX ≤ (C.length / 2) * (k + 1) ∧
      eSX ≤ (C.length / 2) * (C.length - C.length / 2) := by
  classical
  obtain ⟨H, S, T, U, hGH, hST, hSU, hTU, hpart,
      hScard, hTcard, hUcard, hAdj, hSsub, hTdiff⟩ :=
    ext_rich_host2 C (by simpa [hcard] using hW)
  let R := Finset.univ \ S
  let X := C.vertexFinset \ S
  let O := Finset.univ \ C.vertexFinset
  let eS := (G.induce (↑S : Set V)).edgeFinset.card
  have hXS : Disjoint X S := Finset.disjoint_sdiff.symm
  let crossXS := (edgesBetween G X S).card
  have hRpart : R = X ∪ O := by
    ext x
    simp only [R, X, O, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union]
    tauto
  have hXO : Disjoint X O := by
    apply Finset.disjoint_left.mpr
    intro x hxX hxO
    exact (Finset.mem_sdiff.mp hxO).2 (Finset.mem_sdiff.mp hxX).1
  have hRS : Disjoint R S := Finset.disjoint_sdiff.symm
  have hCrossTotal : (edgesBetween G R S).card ≤
      crossXS + O.card * S.card := by
    rw [edgesBetween_card_eq_sum_neighborsIn R S hRS, hRpart,
      Finset.sum_union hXO]
    have hXsum : (∑ x ∈ X, (neighborsIn G x S).card) = crossXS := by
      dsimp [crossXS]
      exact (edgesBetween_card_eq_sum_neighborsIn X S hXS).symm
    rw [hXsum]
    apply Nat.add_le_add_left
    simpa [Nat.mul_comm] using O.sum_le_card_nsmul
      (fun x ↦ (neighborsIn G x S).card) S.card
      (fun x hx ↦ Finset.card_le_card (Finset.filter_subset _ _))
  have hOcard : O.card = n - C.length := by
    dsimp [O]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr
      (Finset.subset_univ _), Finset.card_univ, C.card_vertexFinset, hcard]
  have hXcard : X.card = C.length - C.length / 2 := by
    dsimp [X]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSsub,
      C.card_vertexFinset, hScard]
  have hRestEdges : (G.induce (↑R : Set V)).edgeFinset.card ≤ T.card.choose 2 := by
    let K := G.induce (↑R : Set V)
    let TR : Finset R := Finset.univ.filter fun x ↦ (x : V) ∈ T
    have hsupport : K.support ⊆ (↑TR : Set R) := by
      intro x hx
      obtain ⟨y, hxy⟩ := hx
      have hxNotS : (x : V) ∉ S := (Finset.mem_sdiff.mp x.property).2
      have hyNotS : (y : V) ∉ S := (Finset.mem_sdiff.mp y.property).2
      have hxyH : H.Adj (x : V) (y : V) := hGH hxy
      have hxT : (x : V) ∈ T := by
        rcases (hAdj (x : V) (y : V)).mp hxyH with ⟨_, hcases⟩
        rcases hcases with hboth | hxU | hxS
        · rcases Finset.mem_union.mp hboth.1 with hxS' | hxT
          · exact (hxNotS hxS').elim
          · exact hxT
        · exact (hyNotS hxU.2).elim
        · exact (hxNotS hxS.1).elim
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxT⟩
    have htriv' : K.edgeFinset.card ≤ TR.card.choose 2 := by
      have hsupportCard : Fintype.card K.support ≤ TR.card := by
        rw [Set.fintypeCard_eq_ncard, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsupport
      have hchooseSupport := Nat.choose_le_choose 2 hsupportCard
      calc
        K.edgeFinset.card =
            (K.induce K.support).edgeFinset.card :=
          K.card_edgeFinset_induce_support.symm
        _ ≤ (Fintype.card K.support).choose 2 :=
          (K.induce K.support).card_edgeFinset_le_card_choose_two
        _ ≤ TR.card.choose 2 := hchooseSupport
    have hTRcard : TR.card ≤ T.card := by
      let j : R ↪ V := Function.Embedding.subtype (· ∈ R)
      have hsub : TR.map j ⊆ T := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        exact (Finset.mem_filter.mp ha).2
      calc
        TR.card = (TR.map j).card := by simp
        _ ≤ T.card := Finset.card_le_card hsub
    have hchoose := Nat.choose_le_choose 2 hTRcard
    change K.edgeFinset.card ≤ T.card.choose 2
    exact htriv'.trans hchoose
  have htau1 : 1 ≤ T.card := by rw [hTcard]; omega
  have htau2 : T.card ≤ 2 := by rw [hTcard]; omega
  have hchooseT : T.card.choose 2 = T.card - 1 := by
    interval_cases T.card <;> norm_num at *
  have hdec := edge_count_finset_decomposition G S
  change G.edgeFinset.card = eS +
    ((G.induce (↑R : Set V)).edgeFinset.card +
      (edgesBetween G R S).card) at hdec
  have hedge : G.edgeFinset.card ≤
      crossXS + eS + (C.length / 2) * (n - C.length) + T.card - 1 := by
    rw [hchooseT] at hRestEdges
    rw [hOcard, hScard] at hCrossTotal
    calc
      G.edgeFinset.card = eS +
          ((G.induce (↑R : Set V)).edgeFinset.card +
            (edgesBetween G R S).card) := hdec
      _ ≤ eS + ((T.card - 1) +
          (crossXS + (n - C.length) * (C.length / 2))) := by
        exact Nat.add_le_add_left
          (Nat.add_le_add hRestEdges hCrossTotal) eS
      _ = crossXS + eS + (C.length / 2) *
          (n - C.length) + T.card - 1 := by
        rw [Nat.mul_comm (n - C.length) (C.length / 2)]
        omega
  have hdegree := cycle_partition_degree_bound hfree C S hSsub
  have hcrossRename : crossXS = (edgesBetween G S X).card := by
    dsimp [crossXS]
    apply congrArg Finset.card
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [edgesBetween, Finset.mem_filter]
        constructor
        · rintro ⟨he, a, haX, b, hbS, hab⟩
          exact ⟨he, b, hbS, a, haX, hab.trans Sym2.eq_swap⟩
        · rintro ⟨he, a, haS, b, hbX, hab⟩
          exact ⟨he, b, hbX, a, haS, hab.trans Sym2.eq_swap⟩
  rw [← hcrossRename] at hdegree
  have hcrossMax : crossXS ≤ S.card * X.card := by
    dsimp [crossXS]
    rw [edgesBetween_card_eq_sum_neighborsIn X S hXS]
    simpa [Nat.mul_comm] using X.sum_le_card_nsmul
      (fun x ↦ (neighborsIn G x S).card) S.card
      (fun x hx ↦ Finset.card_le_card (Finset.filter_subset _ _))
  rw [hScard, hXcard] at hcrossMax
  exact ⟨eS, crossXS, T.card, hTcard, htau1, htau2, hedge,
    by simpa [eS, hScard] using hdegree, hcrossMax⟩

/-- In the exterior-rich subcase of Ma--Ning alternative (ii), the canonical
host structure and the path-fan degree bounds imply the required extremal
edge bound. -/
theorem cycle_case_ii_rich_edge_bound
    (lit : LiteratureTheorems.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hnUpper : n ≤ (5 * k + 2) / 2)
    (hcard : Fintype.card V = n) (hfree : PathFanFree G (k + 2))
    (C : CycleWitness G) (h2c : IsTwoConnected G)
    (hlongest : IsLongestCycle C)
    (hcycleLower : 2 * ((k + 1) / 2) + 2 ≤ C.length)
    (hcn : C.length < n) (hc10 : 10 ≤ C.length)
    (hmin : (k + 1) / 2 + 1 ≤ G.minDegree)
    (hrich :
      (C.length / 2 - 1) * (n - C.length) <
        (G.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
          (edgesBetween G (Finset.univ \ C.vertexFinset)
            C.vertexFinset).card) :
    G.edgeFinset.card ≤ h k n := by
  have hnUpper' : Fintype.card V ≤ (5 * k + 2) / 2 := by
    omega
  have hcn' : C.length < Fintype.card V := by omega
  have hrich' :
      (C.length / 2 - 1) * (Fintype.card V - C.length) <
        (G.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
          (edgesBetween G (Finset.univ \ C.vertexFinset)
            C.vertexFinset).card := by
    simpa [hcard] using hrich
  have hWcard := ext_rich_host1_of_literature lit G C hk hnUpper'
    h2c hlongest hc10 hcn' hmin hrich'
  have hqA := ext_rich_edge_bound hfree C hcycleLower hWcard hrich'
  have hWn : IsSubgraphOfW G n (C.length / 2) C.length := by
    simpa [hcard] using hWcard
  obtain ⟨eS, eSX, tau, htau, htau1, htau2, hedge, hdegree, hcross⟩ :=
    rich_host_accounting hcard hfree C hWn
  have hp : G.edgeFinset.card ≤ p k n :=
    rich_host_arithmetic rfl htau htau1 htau2 hcn hqA
      hedge hdegree hcross
  exact hp.trans (p_le_h hn)

end

end Erdos767
