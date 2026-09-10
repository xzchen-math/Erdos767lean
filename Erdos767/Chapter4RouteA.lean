import Erdos767.LiteratureTheorems

/-!
# Chapter 4 deductions under the Route-A literature interface

Every theorem in this file is kernel-checked.  Cited results enter only
through an explicit argument `lit : LiteratureTheorems`.
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

local instance routeAClassicalDecidableAdj {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj := Classical.decRel _

section ClosureIteration

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (r : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem closureIterate_zero : closureIterate r G 0 = G := rfl

@[simp] theorem closureIterate_succ (i : ℕ) :
    closureIterate r G (i + 1) =
      closureStep r (closureIterate r G i) := rfl

theorem closureIterate_le_succ (i : ℕ) :
    closureIterate r G i ≤ closureIterate r G (i + 1) := by
  rw [closureIterate_succ]
  exact le_closureStep r _

theorem le_closureIterate (i : ℕ) :
    G ≤ closureIterate r G i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      exact ih.trans (closureIterate_le_succ r G i)

theorem le_rClosure : G ≤ rClosure r G := by
  exact le_closureIterate r G _

theorem closureIterate_add (i j : ℕ) :
    closureIterate r G (i + j) =
      closureIterate r (closureIterate r G i) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ, closureIterate_succ, ih, closureIterate_succ]

theorem closureIterate_constant_of_fixed {i : ℕ}
    (hfix : closureIterate r G (i + 1) = closureIterate r G i)
    (j : ℕ) :
    closureIterate r G (i + j) = closureIterate r G i := by
  have hstep : closureStep r (closureIterate r G i) =
      closureIterate r G i := by
    simpa [closureIterate_succ] using hfix
  rw [closureIterate_add]
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [closureIterate_succ, ih, hstep]

theorem closureIterate_strict_card {i : ℕ}
    (hne : closureIterate r G (i + 1) ≠ closureIterate r G i) :
    (closureIterate r G i).edgeFinset.card <
      (closureIterate r G (i + 1)).edgeFinset.card := by
  apply Finset.card_lt_card
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset]
  exact lt_of_le_of_ne (closureIterate_le_succ r G i) (Ne.symm hne)

private theorem index_le_edgeCard_of_no_fixed
    (M : ℕ)
    (hno : ∀ i, i ≤ M →
      closureIterate r G (i + 1) ≠ closureIterate r G i) :
    ∀ i, i ≤ M + 1 → i ≤ (closureIterate r G i).edgeFinset.card := by
  intro i hi
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hiM : i ≤ M := by omega
      have hcard := closureIterate_strict_card r G (hno i hiM)
      have hprev : i ≤ (closureIterate r G i).edgeFinset.card :=
        ih (by omega)
      omega

/-- After at most `choose |V| 2` steps the simultaneous closure process is
at a fixed point. -/
theorem rClosure_fixed : closureStep r (rClosure r G) = rClosure r G := by
  let M := (Fintype.card V).choose 2
  change closureIterate r G (M + 1) = closureIterate r G M
  by_contra hlast
  have hno : ∀ i, i ≤ M →
      closureIterate r G (i + 1) ≠ closureIterate r G i := by
    intro i hi hfixed
    have hM := closureIterate_constant_of_fixed r G hfixed (M - i)
    have hM1 := closureIterate_constant_of_fixed r G hfixed (M + 1 - i)
    have hiM' : i + (M - i) = M := by omega
    have hiM1' : i + (M + 1 - i) = M + 1 := by omega
    rw [hiM'] at hM
    rw [hiM1'] at hM1
    exact hlast (hM1.trans hM.symm)
  have hlower : M + 1 ≤
      (closureIterate r G (M + 1)).edgeFinset.card :=
    index_le_edgeCard_of_no_fixed r G M hno (M + 1) (by omega)
  have hupper : (closureIterate r G (M + 1)).edgeFinset.card ≤ M := by
    exact SimpleGraph.card_edgeFinset_le_card_choose_two
  omega

/-- The graph produced by `rClosure` is degree-sum closed. -/
theorem rClosure_isRClosed : IsRClosed r (rClosure r G) := by
  exact (closureStep_eq_self_iff r (rClosure r G)).mp (rClosure_fixed r G)

end ClosureIteration

section CycleCoreClosure

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A partition with the prescribed sizes realizes the canonical `W` host. -/
theorem isWGraph_wGraphFromPartition
    {n s t : ℕ} {S T U : Finset V}
    (hn : Fintype.card V = n)
    (hs1 : 1 ≤ s) (hst : s ≤ (t + 1) / 2) (htn : t - s + 1 ≤ n)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hcover : S ∪ T ∪ U = Finset.univ)
    (hScard : S.card = s) (hTcard : T.card = t - 2 * s + 1)
    (hUcard : U.card = n - t + s - 1) :
    IsWGraph (wGraphFromPartition S T U) n s t := by
  exact ⟨hn, hs1, hst, htn, S, T, U, hST, hSU, hTU,
    hcover, hScard, hTcard, hUcard, fun _ _ ↦ Iff.rfl⟩

/-- A cycle has exactly `length` distinct vertices. -/
theorem CycleWitness.card_vertexFinset (C : CycleWitness G) :
    C.vertexFinset.card = C.length := by
  have hbase : C.base ∈ C.walk.support.tail :=
    C.walk.end_mem_tail_support C.isCycle.not_nil
  have htail : C.walk.tail.support = C.walk.support.tail :=
    C.walk.support_tail_of_not_nil C.isCycle.not_nil
  have hbase' : C.base ∈ C.walk.tail.support := by
    rw [htail]
    exact hbase
  have hbaseFin : C.base ∈ C.walk.tail.support.toFinset := by
    simpa using hbase'
  have hnodup : C.walk.tail.support.Nodup := by
    rw [htail]
    exact C.isCycle.support_nodup
  have hlen : C.walk.support.tail.length = C.walk.length := by
    rw [List.length_tail, C.walk.length_support]
    omega
  rw [CycleWitness.vertexFinset, ← C.walk.cons_support_tail C.isCycle.not_nil]
  simp only [List.toFinset_cons, Finset.insert_eq_of_mem hbaseFin]
  rw [List.toFinset_card_of_nodup hnodup, htail, hlen]
  rfl

/-- Cardinality of the subtype used for the closed cycle core. -/
theorem CycleWitness.card_vertexSubtype (C : CycleWitness G) :
    Fintype.card {x // x ∈ C.vertexFinset} = C.length := by
  simpa using C.card_vertexFinset

/-- The internal graph in the `C`-closure is `(c+1)`-closed. -/
theorem cycleCoreClosure_isRClosed (C : CycleWitness G) :
    IsRClosed (C.length + 1) (cycleCoreClosure C) := by
  exact rClosure_isRClosed (C.length + 1)
    (G.induce (↑C.vertexFinset : Set V))

/-- The original graph induced on `C` is contained in its closed core. -/
theorem induceCycle_le_cycleCoreClosure (C : CycleWitness G) :
    G.induce (↑C.vertexFinset : Set V) ≤ cycleCoreClosure C := by
  exact le_rClosure (C.length + 1) _

/-- The cycle itself forces minimum degree at least two in its closed core. -/
theorem two_le_cycleCoreClosure_minDegree (C : CycleWitness G) :
    2 ≤ (cycleCoreClosure C).minDegree := by
  classical
  letI : Nonempty {x // x ∈ C.vertexFinset} :=
    ⟨⟨C.base, C.base_mem_vertexFinset⟩⟩
  apply (cycleCoreClosure C).le_minDegree_of_forall_le_degree
  intro x
  let x₀ : C.walk.toSubgraph.verts :=
    ⟨x, by
      rw [C.walk.mem_verts_toSubgraph]
      simpa [CycleWitness.vertexFinset] using x.property⟩
  let f : C.walk.toSubgraph.coe →g
      G.induce (↑C.vertexFinset : Set V) :=
    { toFun := fun y ↦
        ⟨y, by
          rw [CycleWitness.vertexFinset]
          exact List.mem_toFinset.mpr
            (C.walk.mem_verts_toSubgraph.mp y.property)⟩
      map_rel' := by
        intro a b hab
        exact C.walk.toSubgraph.coe_adj_sub a b hab }
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg
      (fun z : {x // x ∈ C.vertexFinset} ↦ (z : V)) hab
  have hxmem : (x : V) ∈ C.walk.support := by
    simpa [CycleWitness.vertexFinset] using x.property
  have hsubDegree : C.walk.toSubgraph.coe.degree x₀ = 2 := by
    rw [SimpleGraph.Subgraph.coe_degree]
    unfold SimpleGraph.Subgraph.degree
    rw [Set.fintypeCard_eq_ncard]
    exact C.isCycle.ncard_neighborSet_toSubgraph_eq_two hxmem
  have hdegreeInduced : 2 ≤
      (G.induce (↑C.vertexFinset : Set V)).degree x := by
    have hmap := (f.toCopy hfInjective).degree_le x₀
    have hfx : f x₀ = x := by
      apply Subtype.ext
      rfl
    rw [hsubDegree] at hmap
    change 2 ≤ (G.induce (↑C.vertexFinset : Set V)).degree (f x₀) at hmap
    rw [hfx] at hmap
    exact hmap
  exact hdegreeInduced.trans
    ((G.induce (↑C.vertexFinset : Set V)).degree_le_of_le
      (induceCycle_le_cycleCoreClosure C))

/-- The original graph is a spanning subgraph of its `C`-closure. -/
theorem le_cycleClosure (C : CycleWitness G) : G ≤ cycleClosure C := by
  exact le_sup_left

/-- On the vertices of `C`, the full `C`-closure is exactly the closed core. -/
theorem cycleClosure_induce_cycle_eq (C : CycleWitness G) :
    (cycleClosure C).induce (↑C.vertexFinset : Set V) =
      cycleCoreClosure C := by
  classical
  ext x y
  change G.Adj x y ∨
      ((cycleCoreClosure C).map
        (Function.Embedding.subtype (· ∈ C.vertexFinset))).Adj x y ↔
      (cycleCoreClosure C).Adj x y
  constructor
  · rintro (hxy | hxy)
    · exact induceCycle_le_cycleCoreClosure C hxy
    · simpa using
        (SimpleGraph.map_adj_apply
          (G := cycleCoreClosure C)
          (f := Function.Embedding.subtype (· ∈ C.vertexFinset))
          (a := x) (b := y)).mp hxy
  · intro hxy
    exact Or.inr <| by
      simpa using
        (SimpleGraph.map_adj_apply
          (G := cycleCoreClosure C)
          (f := Function.Embedding.subtype (· ∈ C.vertexFinset))
          (a := x) (b := y)).mpr hxy

/-- Outside `C`, closure adds no edge. -/
theorem cycleClosure_induce_outside_eq (C : CycleWitness G) :
    (cycleClosure C).induce
        (↑(Finset.univ \ C.vertexFinset) : Set V) =
      G.induce (↑(Finset.univ \ C.vertexFinset) : Set V) := by
  classical
  ext x y
  change G.Adj x y ∨
      ((cycleCoreClosure C).map
        (Function.Embedding.subtype (· ∈ C.vertexFinset))).Adj x y ↔
      G.Adj x y
  constructor
  · rintro (hxy | hxy)
    · exact hxy
    · obtain ⟨u, v, huv, hu, hv⟩ :=
        (SimpleGraph.map_adj _ _ _ _).mp hxy
      have hxOutside : (x : V) ∉ C.vertexFinset := by
        simpa using x.property
      exact (hxOutside (hu ▸ u.property)).elim
  · exact Or.inl

/-- Adding edges preserves the manuscript's finite 2-connectivity predicate. -/
theorem IsTwoConnected.mono {H K : SimpleGraph V}
    (hHK : H ≤ K) (hH : IsTwoConnected H) : IsTwoConnected K := by
  refine ⟨hH.1, ?_⟩
  intro x
  apply (hH.2 x).mono
  intro u v huv
  exact hHK huv

end CycleCoreClosure

section ExceptionalHosts

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The `Y`-family side of `lem:exceptional-low-degree-or-W`: every
admissible nontrivial star forest supplies a leaf of degree at most three. -/
theorem IsYGraph.exists_degree_le_three {n c : ℕ}
    (hY : IsYGraph G n c) : ∃ x : V, G.degree x ≤ 3 := by
  classical
  rcases hY with
    ⟨_, _, A, B, Y, _, _, _, _, _, _, _, _, F,
      a, haA, b, hbA, hab, hExternal, hLarge⟩
  have hmpos : 0 < F.componentCount := by
    exact lt_of_lt_of_le (by decide : 0 < 2) F.two_le_componentCount
  let i : Fin F.componentCount := ⟨0, hmpos⟩
  have hpartNontrivial : (F.part i).Nontrivial :=
    Finset.one_lt_card.mp (F.component_nontrivial i)
  obtain ⟨x, hxPart, hxne⟩ :=
    hpartNontrivial.exists_ne (F.center i)
  by_cases hlarge : 3 ≤ (F.part i).card
  · obtain ⟨z, hz, hzDegree⟩ := hLarge i hlarge
    have hxDegree : G.degree x = 2 :=
      (hzDegree x (Finset.mem_erase.mpr ⟨hxne, hxPart⟩)).1
    exact ⟨x, by omega⟩
  · have hxY : x ∈ Y := (F.covers x).2 ⟨i, hxPart⟩
    have hneighborSubset :
        G.neighborFinset x ⊆ {F.center i, a, b} := by
      intro y hy
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
      by_cases hyPart : y ∈ F.part i
      · have hyY : y ∈ Y := (F.covers y).2 ⟨i, hyPart⟩
        obtain ⟨j, hxj, hyj, hstar⟩ :=
          (F.induced_adj x hxY y hyY).mp hxy
        have hji : j = i := by
          by_contra hne
          have hdis := F.pairwise_disjoint i j (Ne.symm hne)
          exact (Finset.disjoint_left.mp hdis hxPart hxj)
        subst j
        rcases hstar with hcenter | hcenter
        · exact (hxne hcenter.1).elim
        · simp [hcenter.1]
      · have hyExternal : y ∈ externalNeighbors G (F.part i) := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, hyPart,
            ⟨x, hxPart, hxy.symm⟩⟩
        rw [hExternal i] at hyExternal
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyExternal
        rcases hyExternal with rfl | rfl <;> simp
    refine ⟨x, ?_⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset x).card ≤ ({F.center i, a, b} : Finset V).card :=
        Finset.card_le_card hneighborSubset
      _ ≤ ({a, b} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 + 1 := Nat.add_le_add_right (by
        calc
          ({a, b} : Finset V).card ≤ ({b} : Finset V).card + 1 :=
            Finset.card_insert_le _ _
          _ = 2 := by simp) 1
      _ = 3 := rfl

/-- The `X`-family side of `lem:exceptional-low-degree-or-W`. -/
theorem IsXGraph.subgraphOfW_or_exists_degree_le_three
    {n c : ℕ} (hcn : c < n) (hX : IsXGraph G n c) :
    IsSubgraphOfW G n (c / 2) c ∨ ∃ x : V, G.degree x ≤ 3 := by
  classical
  rcases hX with
    ⟨hn, hcOdd, A, B, X, hAB, hAX, hBX, hcover, hAcard,
      hAclique, hBindep, hXindep, hABcomplete,
      a, haA, b, hbB, hab, hXneighbors⟩
  have hcmod : c % 2 = 1 := Nat.odd_iff.mp hcOdd
  by_cases hXempty : X = ∅
  · have hABcover : A ∪ B = Finset.univ := by
      simpa [hXempty] using hcover
    have hcardAB : A.card + B.card = n := by
      calc
        A.card + B.card = (A ∪ B).card :=
          (Finset.card_union_of_disjoint hAB).symm
        _ = Fintype.card V := by rw [hABcover, Finset.card_univ]
        _ = n := hn
    have hBcard : B.card = n - c / 2 := by omega
    have hBtwo : 2 ≤ B.card := by
      have haCardPos : 0 < A.card := Finset.card_pos.mpr ⟨a, haA⟩
      rw [hAcard] at haCardPos
      omega
    obtain ⟨T, hTsub, hTcardTwo⟩ :=
      Finset.exists_subset_card_eq hBtwo
    let U := B \ T
    let H := wGraphFromPartition A T U
    have hAT : Disjoint A T := hAB.mono_right hTsub
    have hAU : Disjoint A U :=
      hAB.mono_right (Finset.sdiff_subset.trans (le_refl B))
    have hTU : Disjoint T U := Finset.disjoint_sdiff
    have hpartition : A ∪ T ∪ U = Finset.univ := by
      dsimp [U]
      rw [Finset.union_assoc, Finset.union_sdiff_of_subset hTsub,
        hABcover]
    have hsOne : 1 ≤ c / 2 := by
      have : 0 < A.card := Finset.card_pos.mpr ⟨a, haA⟩
      omega
    have hsUpper : c / 2 ≤ (c + 1) / 2 := by omega
    have hsizeCondition : c - c / 2 + 1 ≤ n := by
      calc
        c - c / 2 + 1 ≤ c + 1 :=
          Nat.add_le_add_right (Nat.sub_le c (c / 2)) 1
        _ ≤ n := by omega
    have hTcard : T.card = c - 2 * (c / 2) + 1 := by
      rw [hTcardTwo]
      omega
    have hUcard : U.card = n - c + c / 2 - 1 := by
      dsimp [U]
      rw [Finset.card_sdiff_of_subset hTsub, hBcard, hTcardTwo]
      omega
    have hHisW : IsWGraph H n (c / 2) c := by
      exact isWGraph_wGraphFromPartition hn hsOne hsUpper hsizeCondition
        hAT hAU hTU hpartition hAcard hTcard hUcard
    have hGleH : G ≤ H := by
      intro x y hxy
      have hxAB : x ∈ A ∨ x ∈ B := by
        have : x ∈ A ∪ B := by rw [hABcover]; simp
        simpa using this
      have hyAB : y ∈ A ∨ y ∈ B := by
        have : y ∈ A ∪ B := by rw [hABcover]; simp
        simpa using this
      refine (wGraphFromPartition_adj).2 ⟨hxy.ne, ?_⟩
      rcases hxAB with hxA | hxB <;> rcases hyAB with hyA | hyB
      · exact Or.inl ⟨Finset.mem_union_left _ hxA,
          Finset.mem_union_left _ hyA⟩
      · by_cases hyT : y ∈ T
        · exact Or.inl ⟨Finset.mem_union_left _ hxA,
            Finset.mem_union_right _ hyT⟩
        · exact Or.inr (Or.inr ⟨hxA,
            Finset.mem_sdiff.mpr ⟨hyB, hyT⟩⟩)
      · by_cases hxT : x ∈ T
        · exact Or.inl ⟨Finset.mem_union_right _ hxT,
            Finset.mem_union_left _ hyA⟩
        · exact Or.inr (Or.inl
            ⟨Finset.mem_sdiff.mpr ⟨hxB, hxT⟩, hyA⟩)
      · exact (hBindep hxB hyB hxy.ne) hxy |>.elim
    exact Or.inl ⟨H, hHisW, hGleH⟩
  · obtain ⟨x, hxX⟩ := Finset.nonempty_iff_ne_empty.mpr hXempty
    have hxNeighbors := hXneighbors x hxX
    refine Or.inr ⟨x, ?_⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hxNeighbors]
    calc
      ({a, b} : Finset V).card ≤ ({b} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
      _ ≤ 3 := by omega

/-- Manuscript Lemma `lem:exceptional-low-degree-or-W`. -/
theorem exceptional_low_degree_or_W
    {n c : ℕ} (hcn : c < n)
    (hExceptional : IsXGraph G n c ∨ IsYGraph G n c) :
    IsSubgraphOfW G n (c / 2) c ∨ ∃ x : V, G.degree x ≤ 3 := by
  rcases hExceptional with hX | hY
  · exact hX.subgraphOfW_or_exists_degree_le_three hcn
  · exact Or.inr hY.exists_degree_le_three

end ExceptionalHosts

section DegreeCliqueDichotomy

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Vertices whose degree is at most `s`. -/
def lowDegreeVertices (H : SimpleGraph W) [DecidableRel H.Adj]
    (s : ℕ) : Finset W :=
  Finset.univ.filter fun x ↦ H.degree x ≤ s

/-- The two alternatives in the manuscript's variant of Ma--Ning
Lemma 2.11, stated for an arbitrary closed graph. -/
def DegreeCliqueDichotomy (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  (∃ s : ℕ, ∃ S : Finset W,
      2 ≤ s ∧ s ≤ Fintype.card W / 2 - 1 ∧
      S.card = s - 1 ∧
      (∀ x ∈ S, H.degree x ≤ s) ∧
      H.IsClique (↑(Finset.univ \ S) : Set W)) ∨
    ∃ R : Finset W,
      R.card = Fintype.card W / 2 - 1 ∧
      ∀ x ∈ R, H.degree x ≤ Fintype.card W / 2

/-- The degree-sequence argument in the proof of
`lem:Ma-Ning-cycle-dichotomy`.  This is a paper-specific deduction from
Ma--Ning Lemma 2.10 plus closedness; it is not an additional assumption. -/
theorem degreeCliqueDichotomy_of_literature
    (lit : LiteratureTheorems.{u})
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnonham : ¬ IsHamiltonianConnected H)
    (hmin : 2 ≤ H.minDegree)
    (hclosed : IsRClosed (Fintype.card W + 1) H) :
    DegreeCliqueDichotomy H := by
  classical
  let q := Fintype.card W / 2
  let low : ℕ → Finset W := fun a ↦ lowDegreeVertices H a
  let candidates : Finset ℕ :=
    (Finset.Icc 2 q).filter fun a ↦ a - 1 ≤ (low a).card
  obtain ⟨s₀, hs₀2, hs₀q, S₀, hS₀card, hS₀deg⟩ :=
    lit.maNingDegree H hnonham hmin
  have hS₀sub : S₀ ⊆ low s₀ := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS₀deg x hx⟩
  have hs₀low : s₀ - 1 ≤ (low s₀).card :=
    hS₀card.trans (Finset.card_le_card hS₀sub)
  have hs₀mem : s₀ ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hs₀2, hs₀q⟩, hs₀low⟩
  have hcandidates : candidates.Nonempty := ⟨s₀, hs₀mem⟩
  obtain ⟨s, hsCand, hsMax⟩ :=
    Finset.exists_max_image candidates id hcandidates
  simp only [id_eq] at hsMax
  have hsIcc := (Finset.mem_filter.mp hsCand).1
  have hsBounds : 2 ≤ s ∧ s ≤ q := Finset.mem_Icc.mp hsIcc
  have hsLow : s - 1 ≤ (low s).card :=
    (Finset.mem_filter.mp hsCand).2
  by_cases hsq : s = q
  · right
    have hqLow : q - 1 ≤ (low q).card := by simpa [hsq] using hsLow
    obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hqLow
    refine ⟨R, ?_, ?_⟩
    · simpa [q] using hRcard
    · intro x hx
      have hxlow := hRsub hx
      exact (Finset.mem_filter.mp hxlow).2
  · have hsqLt : s < q := lt_of_le_of_ne hsBounds.2 hsq
    have hcardLow : (low s).card = s - 1 := by
      have hnot : ¬ s ≤ (low s).card := by
        intro hsCard
        have hmono : low s ⊆ low (s + 1) := by
          intro x hx
          have hxdeg := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have hnextLow : s ≤ (low (s + 1)).card :=
          hsCard.trans (Finset.card_le_card hmono)
        have hnextMem : s + 1 ∈ candidates := by
          apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_Icc.mpr
            constructor <;> omega
          · simpa using hnextLow
        have := hsMax (s + 1) hnextMem
        omega
      omega
    let B : Finset W := Finset.univ \ low s
    by_cases hclique : H.IsClique (↑B : Set W)
    · left
      refine ⟨s, low s, hsBounds.1, ?_, hcardLow, ?_, ?_⟩
      · dsimp [q] at hsqLt ⊢
        omega
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · simpa only [B, Finset.coe_sdiff, Finset.coe_univ] using hclique
    · have hnotClique := (not_isClique_iff H).mp hclique
      obtain ⟨u₀, v₀, huv₀, hnonadj₀⟩ := hnotClique
      have hu₀B : (u₀ : W) ∈ B := by simpa using u₀.property
      have hv₀B : (v₀ : W) ∈ B := by simpa using v₀.property
      let M : Finset W := B.filter fun x ↦
        ∃ y ∈ B, x ≠ y ∧ ¬ H.Adj x y
      have hu₀M : (u₀ : W) ∈ M := by
        apply Finset.mem_filter.mpr
        exact ⟨hu₀B, ⟨v₀, hv₀B, by simpa, hnonadj₀⟩⟩
      have hMnonempty : M.Nonempty := ⟨u₀, hu₀M⟩
      obtain ⟨u, huM, huMax⟩ :=
        Finset.exists_max_image M (fun x ↦ H.degree x) hMnonempty
      obtain ⟨huB, v, hvB, huv, huvNonadj⟩ := Finset.mem_filter.mp huM
      let Sprime : Finset W :=
        Finset.univ \ (H.neighborFinset u ∪ {u})
      have hdeglt : H.degree u < Fintype.card W := H.degree_lt_card_verts u
      have huNotNeigh : u ∉ H.neighborFinset u := by simp
      have hcardUnion : (H.neighborFinset u ∪ {u}).card = H.degree u + 1 := by
        rw [Finset.card_union_of_disjoint]
        · simp [SimpleGraph.card_neighborFinset_eq_degree]
        · exact Finset.disjoint_singleton_right.mpr huNotNeigh
      have hcardSprime : Sprime.card = Fintype.card W - (H.degree u + 1) := by
        dsimp [Sprime]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        simpa [hcardUnion]
      let sprime := Sprime.card + 1
      have hsprimeEq : sprime = Fintype.card W - H.degree u := by
        dsimp [sprime]
        rw [hcardSprime]
        omega
      have hSprimeDeg : ∀ w ∈ Sprime, H.degree w ≤ sprime := by
        intro w hw
        have hwmem := Finset.mem_sdiff.mp hw
        have hwNotUnion := hwmem.2
        have hwu : w ≠ u := by
          intro h
          subst w
          exact hwNotUnion (by simp)
        have hnonadj : ¬ H.Adj u w := by
          intro hadj
          exact hwNotUnion (Finset.mem_union_left _
            ((H.mem_neighborFinset u w).mpr hadj))
        have hsum := hclosed u w hwu.symm hnonadj
        rw [hsprimeEq]
        omega
      have hvSprime : v ∈ Sprime := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hvUnion
        rcases Finset.mem_union.mp hvUnion with hvNeigh | hvEq
        · exact huvNonadj ((H.mem_neighborFinset u v).mp hvNeigh)
        · have : v = u := by simpa using hvEq
          exact huv this.symm
      have hvNotLow : v ∉ low s := by
        intro hvlow
        exact (Finset.mem_sdiff.mp hvB).2 hvlow
      have hsLtSprime : s < sprime := by
        have hsv : H.degree v ≤ sprime := hSprimeDeg v hvSprime
        have hsv' : s < H.degree v := by
          have hnot : ¬ H.degree v ≤ s := by
            intro hle
            exact hvNotLow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
          omega
        omega
      have hqLtSprime : q < sprime := by
        by_contra hnot
        have hsprimeQ : sprime ≤ q := by omega
        have hnextMem : sprime ∈ candidates := by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_Icc.mpr ⟨by omega, hsprimeQ⟩
          · have : Sprime.card = sprime - 1 := by
              dsimp [sprime]
            rw [← this]
            apply Finset.card_le_card
            intro w hw
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hSprimeDeg w hw⟩
        have := hsMax sprime hnextMem
        omega
      have huDegQ : H.degree u ≤ q := by
        rw [hsprimeEq] at hqLtSprime
        dsimp [q] at hqLtSprime ⊢
        omega
      have hAllSprimeQ : ∀ w ∈ Sprime, H.degree w ≤ q := by
        intro w hw
        by_cases hwlow : w ∈ low s
        · have hws := (Finset.mem_filter.mp hwlow).2
          exact hws.trans hsBounds.2
        · have hwB : w ∈ B := by
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwlow⟩
          have hwu : w ≠ u := by
            intro h
            subst w
            have hwmem := (Finset.mem_sdiff.mp hw).2
            exact hwmem (by simp)
          have hnonadj : ¬ H.Adj w u := by
            intro hadj
            have hwmem := (Finset.mem_sdiff.mp hw).2
            exact hwmem (Finset.mem_union_left _
              ((H.mem_neighborFinset u w).mpr hadj.symm))
          have hwM : w ∈ M := by
            exact Finset.mem_filter.mpr
              ⟨hwB, ⟨u, huB, hwu, hnonadj⟩⟩
          exact (huMax w hwM).trans huDegQ
      have hRsize : q - 1 ≤ Sprime.card := by
        dsimp [sprime] at hqLtSprime
        omega
      obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hRsize
      right
      refine ⟨R, ?_, ?_⟩
      · simpa [q] using hRcard
      · intro x hx
        exact hAllSprimeQ x (hRsub hx)

/-- The manuscript's `lem:Ma-Ning-cycle-dichotomy`, obtained by applying
the proved closed-graph degree dichotomy to the closed core of `C`. -/
theorem maNing_cycle_dichotomy
    (lit : LiteratureTheorems.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : CycleWitness G)
    (h2c : IsTwoConnected G)
    (hloc : IsLocallyMaximalCycle C)
    (hlt : C.length < Fintype.card V) :
    DegreeCliqueDichotomy (cycleCoreClosure C) := by
  apply degreeCliqueDichotomy_of_literature lit (cycleCoreClosure C)
  · exact lit.maNingNonHamiltonianConnected G C h2c hloc hlt
  · exact two_le_cycleCoreClosure_minDegree C
  · have hclosed := cycleCoreClosure_isRClosed C
    simpa [C.card_vertexSubtype] using hclosed

end DegreeCliqueDichotomy

section LiteratureProjections

/-- Route-A projection of Dirac's theorem. -/
theorem dirac_cycle_of_literature (lit : LiteratureTheorems.{u}) :
    DiracCycleTheorem.{u} :=
  lit.diracCycle

/-- Route-A projection of Ma--Ning exterior stability. -/
theorem maNing_exterior_stability_of_literature
    (lit : LiteratureTheorems.{u}) :
    MaNingExteriorStabilityTheorem.{u} :=
  lit.maNingExteriorStability

/-- Route-A projection of Ma--Ning closure preservation. -/
theorem closure_preserves_local_maximality_of_literature
    (lit : LiteratureTheorems.{u}) :
    ClosurePreservesLocalMaximalityTheorem.{u} :=
  lit.closurePreservesLocalMaximality

/-- Route-A projection of Ma--Ning's non-Hamiltonian-connectedness lemma. -/
theorem maNing_nonHamiltonianConnected_of_literature
    (lit : LiteratureTheorems.{u}) :
    MaNingNonHamiltonianConnectedTheorem.{u} :=
  lit.maNingNonHamiltonianConnected

/-- Route-A projection of Ma--Ning's degree lemma. -/
theorem maNing_degree_of_literature (lit : LiteratureTheorems.{u}) :
    MaNingDegreeTheorem.{u} :=
  lit.maNingDegree

/-- Route-A projection of Ma--Ning's strong-attachment lemma. -/
theorem maNing_strong_attachment_of_literature
    (lit : LiteratureTheorems.{u}) :
    MaNingStrongAttachmentTheorem.{u} :=
  lit.maNingStrongAttachment

/-- Route-A projection of Fan--Lv--Wang switching. -/
theorem fanLvWang_switch_of_literature (lit : LiteratureTheorems.{u}) :
    FanLvWangSwitchTheorem.{u} :=
  lit.fanLvWangSwitch

/-- Route-A projection of the Erdős--Gallai path theorem. -/
theorem erdosGallai_path_of_literature (lit : LiteratureTheorems.{u}) :
    ErdosGallaiPathTheorem.{u} :=
  lit.erdosGallaiPath

end LiteratureProjections

end


end Erdos767
