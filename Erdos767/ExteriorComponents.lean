import Erdos767.Switching
import Erdos767.Chapter5RouteA

/-!
# Exterior components and the numerical switching bound

This file supplies the finite component decomposition and the numerical
part of the switching-terminal claim.  Erdős--Gallai is used solely through
the explicit Route-A literature interface.
-/

namespace Erdos767

open SimpleGraph

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : SimpleGraph V} [DecidableRel K.Adj]

local instance (priority := 5) exteriorDecidableAdj (J : SimpleGraph V) :
    DecidableRel J.Adj := Classical.decRel _

def componentOutsideFinset (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    Finset V :=
  c.supp.toFinset.map
    (Function.Embedding.subtype (· ∈
      (↑(Finset.univ \ C.vertexFinset) : Set V)))

theorem componentOutsideFinset_mem_iff
    (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (v : V) :
    v ∈ componentOutsideFinset C c ↔
      ∃ hv : v ∈ Finset.univ \ C.vertexFinset,
        (⟨v, by simpa using hv⟩ :
          ↥(↑(Finset.univ \ C.vertexFinset) : Set V)) ∈ c.supp := by
  classical
  simp only [componentOutsideFinset, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨by simpa using w.property, ?_⟩
    simpa using hw
  · rintro ⟨hv, hvc⟩
    let w : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
      ⟨v, by simpa using hv⟩
    refine ⟨w, ?_, rfl⟩
    simpa [w] using hvc

def componentOutsideEquiv
    (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    c.supp ≃ ↥(↑(componentOutsideFinset C c) : Set V) where
  toFun w := ⟨(w.val.val : V), by
    apply (componentOutsideFinset_mem_iff C c _).mpr
    exact ⟨by simpa using w.val.property, w.property⟩⟩
  invFun v := by
    have hv := (componentOutsideFinset_mem_iff C c v).mp v.property
    exact ⟨⟨v, by simpa using hv.choose⟩, hv.choose_spec⟩
  left_inv w := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

def componentOutsideIso
    (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    c.toSimpleGraph ≃g
      K.induce (↑(componentOutsideFinset C c) : Set V) where
  toEquiv := componentOutsideEquiv C c
  map_rel_iff' := by
    intro a b
    change K.Adj (a.val.val : V) (b.val.val : V) ↔
      K.Adj (a.val.val : V) (b.val.val : V)
    rfl

theorem componentOutsideFinset_isComponent
    (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    IsComponentOutsideCycle C (componentOutsideFinset C c) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := c.nonempty_supp
    refine ⟨w, ?_⟩
    apply (componentOutsideFinset_mem_iff C c _).mpr
    exact ⟨by simpa using w.property, hw⟩
  · intro v hv
    obtain ⟨hvX, hvc⟩ := (componentOutsideFinset_mem_iff C c v).mp hv
    exact hvX
  · exact (componentOutsideIso C c).connected_iff.mp c.connected_toSimpleGraph
  · intro x hxQ y hyX hxy
    obtain ⟨hxX, hxc⟩ := (componentOutsideFinset_mem_iff C c x).mp hxQ
    apply (componentOutsideFinset_mem_iff C c y).mpr
    refine ⟨hyX, ?_⟩
    let xx : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
      ⟨x, by simpa using hxX⟩
    let yy : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
      ⟨y, by simpa using hyX⟩
    have hxyJ : (K.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).Adj xx yy := hxy
    have hxmem : xx ∈ c.supp := by simpa [xx] using hxc
    have := (c.mem_supp_congr_adj hxyJ).mp hxmem
    simpa [yy] using this

theorem biUnion_componentOutsideFinset (C : CycleWitness K) :
    Finset.univ.biUnion (componentOutsideFinset C) =
      Finset.univ \ C.vertexFinset := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨c, hcUniv, hvc⟩ := Finset.mem_biUnion.mp hv
    exact (componentOutsideFinset_isComponent C c).2.1 hvc
  · intro hvX
    let vv : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
      ⟨v, by simpa using hvX⟩
    let c := (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).connectedComponentMk vv
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ _, ?_⟩
    apply (componentOutsideFinset_mem_iff C c v).mpr
    refine ⟨hvX, ?_⟩
    change vv ∈ c.supp
    exact ConnectedComponent.connectedComponentMk_mem

theorem pairwiseDisjoint_componentOutsideFinset (C : CycleWitness K) :
    ((↑(Finset.univ : Finset
      ((K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)) : Set _).Pairwise
      (fun c d => Disjoint (componentOutsideFinset C c)
        (componentOutsideFinset C d))) := by
  classical
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro v hvc hvd
  obtain ⟨hvXc, hvcSupp⟩ := (componentOutsideFinset_mem_iff C c v).mp hvc
  obtain ⟨hvXd, hvdSupp⟩ := (componentOutsideFinset_mem_iff C d v).mp hvd
  let vv : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
    ⟨v, by simpa using hvXc⟩
  have hcMem : vv ∈ c.supp := by simpa [vv] using hvcSupp
  have hdMem : vv ∈ d.supp := by simpa [vv] using hvdSupp
  exact hcd (ConnectedComponent.eq_of_common_vertex hcMem hdMem)

theorem sum_card_componentOutsideFinset (C : CycleWitness K) :
    (∑ c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
        (componentOutsideFinset C c).card) =
      Fintype.card V - C.length := by
  classical
  rw [← Finset.card_biUnion (pairwiseDisjoint_componentOutsideFinset C)]
  rw [biUnion_componentOutsideFinset]
  rw [Finset.card_sdiff]
  simp [C.card_vertexFinset]

/-- A longest path together with its universal maximality property. -/
structure LongestPathData {W : Type u} (J : SimpleGraph W) where
  start : W
  finish : W
  path : J.Walk start finish
  isPath : path.IsPath
  maximal : ∀ (x y : W) (p : J.Walk x y), p.IsPath → p.length ≤ path.length

noncomputable def componentLongestPathData (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    LongestPathData (K.induce
      (↑(componentOutsideFinset C c) : Set V)) := by
  let Q := componentOutsideFinset C c
  have hQ : IsComponentOutsideCycle C (componentOutsideFinset C c) :=
    componentOutsideFinset_isComponent C c
  let z : V := hQ.1.choose
  have hz : z ∈ Q := hQ.1.choose_spec
  letI : Nonempty ↥(↑Q : Set V) := ⟨⟨z, hz⟩⟩
  apply Classical.choice
  obtain ⟨x, y, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length
      (K.induce (↑Q : Set V))
  exact ⟨⟨x, y, p, hp, hmax⟩⟩

def componentLongestPathLength (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) : ℕ :=
  (componentLongestPathData C c).path.length

def componentAttachmentCount (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) : ℕ :=
  (setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset).card

def componentWeight (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) : ℕ :=
  componentLongestPathLength C c + 2 * componentAttachmentCount C c

theorem component_internal_edge_bound (lit : LiteratureTheorems.{u})
    (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    (K.induce (↑(componentOutsideFinset C c) : Set V)).edgeFinset.card ≤
      componentLongestPathLength C c * (componentOutsideFinset C c).card / 2 := by
  classical
  let D := componentLongestPathData C c
  have h := lit.erdosGallaiPath
    (K.induce (↑(componentOutsideFinset C c) : Set V)) D.path.length D.maximal
  simpa [componentLongestPathLength, D, componentLongestPathData] using h

theorem component_neighborsOnCycle_eq
    (C : CycleWitness K) (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)
    (v : V) (hv : v ∈ componentOutsideFinset C c) :
    neighborsIn K v C.vertexFinset =
      setNeighborsIn K (componentOutsideFinset C c) C.vertexFinset := by
  have hQ : IsComponentOutsideCycle C (componentOutsideFinset C c) :=
    componentOutsideFinset_isComponent C c
  ext x
  simp only [neighborsIn, setNeighborsIn, Finset.mem_filter]
  constructor
  · rintro ⟨hxC, hvx⟩
    exact ⟨hxC, v, hv, hvx.symm⟩
  · rintro ⟨hxC, y, hyQ, hxy⟩
    have hvAdj := hterminal
      (componentOutsideFinset C c) hQ x hxC ⟨y, hyQ, hxy⟩ v hv
    exact ⟨hxC, hvAdj.symm⟩

theorem component_crossing_edge_bound
    (C : CycleWitness K) (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    (edgesBetween K (componentOutsideFinset C c) C.vertexFinset).card =
      componentAttachmentCount C c * (componentOutsideFinset C c).card := by
  classical
  have hQ := componentOutsideFinset_isComponent C c
  have hdisj : Disjoint (componentOutsideFinset C c) C.vertexFinset := by
    apply Finset.disjoint_left.mpr
    intro v hvQ hvC
    exact (Finset.mem_sdiff.mp (hQ.2.1 hvQ)).2 hvC
  rw [edgesBetween_card_eq_sum_neighborsIn _ _ hdisj]
  calc
    (∑ v ∈ componentOutsideFinset C c,
        (neighborsIn K v C.vertexFinset).card) =
        ∑ _v ∈ componentOutsideFinset C c,
          componentAttachmentCount C c := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [component_neighborsOnCycle_eq C hterminal c v hv]
            rfl
    _ = componentAttachmentCount C c *
        (componentOutsideFinset C c).card := by
          simp [Nat.mul_comm]

def componentInternalEdgeFinset (C : CycleWitness K)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    Finset (Sym2 V) :=
  {e ∈ K.edgeFinset | e.toFinset ⊆ componentOutsideFinset C c}

theorem pairwiseDisjoint_componentInternalEdgeFinset (C : CycleWitness K) :
    ((↑(Finset.univ : Finset
      ((K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent)) : Set _).Pairwise
      (fun c d => Disjoint (componentInternalEdgeFinset C c)
        (componentInternalEdgeFinset C d))) := by
  classical
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro e hec hed
  have hecSub := (Finset.mem_filter.mp hec).2
  have hedSub := (Finset.mem_filter.mp hed).2
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxc : x ∈ componentOutsideFinset C c := hecSub (by simp)
      have hxd : x ∈ componentOutsideFinset C d := hedSub (by simp)
      obtain ⟨hxXc, hxcSupp⟩ :=
        (componentOutsideFinset_mem_iff C c x).mp hxc
      obtain ⟨hxXd, hxdSupp⟩ :=
        (componentOutsideFinset_mem_iff C d x).mp hxd
      let xx : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
        ⟨x, by simpa using hxXc⟩
      have hcMem : xx ∈ c.supp := by simpa [xx] using hxcSupp
      have hdMem : xx ∈ d.supp := by simpa [xx] using hxdSupp
      exact hcd (ConnectedComponent.eq_of_common_vertex hcMem hdMem)

theorem biUnion_componentInternalEdgeFinset (C : CycleWitness K) :
    Finset.univ.biUnion (componentInternalEdgeFinset C) =
      {e ∈ K.edgeFinset |
        e.toFinset ⊆ Finset.univ \ C.vertexFinset} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨c, hc, hec⟩ := Finset.mem_biUnion.mp he
    have heSub := (Finset.mem_filter.mp hec).2
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hec).1, ?_⟩
    intro x hxe
    exact (componentOutsideFinset_isComponent C c).2.1 (heSub hxe)
  · intro he
    have heK := (Finset.mem_filter.mp he).1
    have heX := (Finset.mem_filter.mp he).2
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxX : x ∈ Finset.univ \ C.vertexFinset := heX (by simp)
        have hyX : y ∈ Finset.univ \ C.vertexFinset := heX (by simp)
        let xx : ↥(↑(Finset.univ \ C.vertexFinset) : Set V) :=
          ⟨x, by simpa using hxX⟩
        let c := (K.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).connectedComponentMk xx
        have hxQ : x ∈ componentOutsideFinset C c := by
          apply (componentOutsideFinset_mem_iff C c x).mpr
          refine ⟨hxX, ?_⟩
          change xx ∈ c.supp
          exact ConnectedComponent.connectedComponentMk_mem
        have hxy : K.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset] using heK
        have hyQ : y ∈ componentOutsideFinset C c :=
          (componentOutsideFinset_isComponent C c).2.2.2
            x hxQ y hyX hxy
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_univ _, Finset.mem_filter.mpr ⟨heK, ?_⟩⟩
        intro z hz
        have hz' : z = x ∨ z = y := by simpa using hz
        rcases hz' with rfl | rfl
        · exact hxQ
        · exact hyQ

theorem sum_component_internal_edges (C : CycleWitness K) :
    (∑ c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
        (K.induce
          (↑(componentOutsideFinset C c) : Set V)).edgeFinset.card) =
      (K.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card := by
  classical
  calc
    (∑ c : (K.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
          (K.induce
            (↑(componentOutsideFinset C c) : Set V)).edgeFinset.card) =
        ∑ c, (componentInternalEdgeFinset C c).card := by
          apply Finset.sum_congr rfl
          intro c hc
          exact (SimpleGraph.card_filter_edgeFinset_toFinset_subset
            (componentOutsideFinset C c)).symm
    _ = (Finset.univ.biUnion
          (componentInternalEdgeFinset C)).card := by
          exact (Finset.card_biUnion
            (pairwiseDisjoint_componentInternalEdgeFinset C)).symm
    _ = {e ∈ K.edgeFinset |
          e.toFinset ⊆ Finset.univ \ C.vertexFinset}.card := by
          rw [biUnion_componentInternalEdgeFinset]
    _ = (K.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card :=
          SimpleGraph.card_filter_edgeFinset_toFinset_subset _

theorem sum_component_crossing_edges
    (C : CycleWitness K) (hterminal : IsSwitchingTerminal K C) :
    (∑ c : (K.induce
      (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
        componentAttachmentCount C c * (componentOutsideFinset C c).card) =
      (edgesBetween K (Finset.univ \ C.vertexFinset)
        C.vertexFinset).card := by
  classical
  have hXC : Disjoint (Finset.univ \ C.vertexFinset) C.vertexFinset := by
    apply Finset.disjoint_left.mpr
    intro x hxX hxC
    exact (Finset.mem_sdiff.mp hxX).2 hxC
  rw [edgesBetween_card_eq_sum_neighborsIn _ _ hXC]
  calc
    (∑ c : (K.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
          componentAttachmentCount C c *
            (componentOutsideFinset C c).card) =
        ∑ c, ∑ v ∈ componentOutsideFinset C c,
          (neighborsIn K v C.vertexFinset).card := by
            apply Finset.sum_congr rfl
            intro c hc
            have hQ := componentOutsideFinset_isComponent C c
            have hdisj : Disjoint (componentOutsideFinset C c)
                C.vertexFinset := by
              apply Finset.disjoint_left.mpr
              intro v hvQ hvC
              exact (Finset.mem_sdiff.mp (hQ.2.1 hvQ)).2 hvC
            exact (component_crossing_edge_bound C hterminal c).symm.trans
              (edgesBetween_card_eq_sum_neighborsIn _ _ hdisj)
    _ = ∑ v ∈ Finset.univ.biUnion (componentOutsideFinset C),
          (neighborsIn K v C.vertexFinset).card :=
        (Finset.sum_biUnion
          (pairwiseDisjoint_componentOutsideFinset C)).symm
    _ = ∑ v ∈ Finset.univ \ C.vertexFinset,
          (neighborsIn K v C.vertexFinset).card := by
        rw [biUnion_componentOutsideFinset]

theorem sum_natDiv_le_natDiv_sum {I : Type u} [DecidableEq I]
    (s : Finset I) (f : I → ℕ) (d : ℕ) :
    (∑ i ∈ s, f i / d) ≤ (∑ i ∈ s, f i) / d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Nat.add_le_add_left ih _).trans
        (Nat.add_div_le_add_div (f a) (∑ i ∈ s, f i) d)

theorem component_incident_edge_bound (lit : LiteratureTheorems.{u})
    (C : CycleWitness K) (hterminal : IsSwitchingTerminal K C)
    (c : (K.induce (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent) :
    (K.induce
        (↑(componentOutsideFinset C c) : Set V)).edgeFinset.card +
      (edgesBetween K (componentOutsideFinset C c)
        C.vertexFinset).card ≤
      componentWeight C c * (componentOutsideFinset C c).card / 2 := by
  have hinternal := component_internal_edge_bound lit C c
  rw [component_crossing_edge_bound C hterminal c]
  apply (Nat.add_le_add_right hinternal
    (componentAttachmentCount C c *
      (componentOutsideFinset C c).card)).trans
  unfold componentWeight
  rw [Nat.add_mul]
  have hid :
      (componentLongestPathLength C c *
          (componentOutsideFinset C c).card +
        2 * componentAttachmentCount C c *
          (componentOutsideFinset C c).card) / 2 =
        componentLongestPathLength C c *
            (componentOutsideFinset C c).card / 2 +
          componentAttachmentCount C c *
            (componentOutsideFinset C c).card := by
    rw [Nat.mul_assoc]
    exact Nat.add_mul_div_left _ _ (by omega)
  rw [hid]

/-- Numerical part of `claim:switching-terminal`: one exterior component
maximizes `ell_i + 2 q_i`, and this maximum controls every edge having at
least one endpoint outside the cycle. -/
theorem switching_terminal_exterior_bound (lit : LiteratureTheorems.{u})
    (C : CycleWitness K) (hlt : C.length < Fintype.card V)
    (hterminal : IsSwitchingTerminal K C) :
    ∃ j : (K.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
      (∀ i, componentWeight C i ≤ componentWeight C j) ∧
      (K.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
        (edgesBetween K (Finset.univ \ C.vertexFinset)
          C.vertexFinset).card ≤
        componentWeight C j * (Fintype.card V - C.length) / 2 := by
  classical
  let X := Finset.univ \ C.vertexFinset
  have hXpos : 0 < X.card := by
    dsimp [X]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [Finset.card_univ, C.card_vertexFinset]
    omega
  obtain ⟨x, hxX⟩ := Finset.card_pos.mp hXpos
  let xx : ↥(↑X : Set V) := ⟨x, by simpa using hxX⟩
  let j₀ := (K.induce (↑X : Set V)).connectedComponentMk xx
  have hnonempty : (Finset.univ : Finset
      ((K.induce (↑X : Set V)).ConnectedComponent)).Nonempty :=
    ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset
      ((K.induce (↑X : Set V)).ConnectedComponent))
    (componentWeight C) hnonempty
  have hmaxAll : ∀ i, componentWeight C i ≤ componentWeight C j := by
    intro i
    exact hmax i (Finset.mem_univ _)
  refine ⟨j, hmaxAll, ?_⟩
  rw [← sum_component_internal_edges C]
  rw [← sum_component_crossing_edges C hterminal]
  rw [← Finset.sum_add_distrib]
  apply le_trans (Finset.sum_le_sum fun i hi => by
    simpa [component_crossing_edge_bound C hterminal i] using
      component_incident_edge_bound lit C hterminal i)
  apply le_trans (Finset.sum_le_sum fun i hi =>
    Nat.div_le_div_right
      (Nat.mul_le_mul_right (componentOutsideFinset C i).card (hmaxAll i)))
  apply le_trans (sum_natDiv_le_natDiv_sum Finset.univ
    (fun i => componentWeight C j * (componentOutsideFinset C i).card) 2)
  have hcards := sum_card_componentOutsideFinset C
  rw [← Finset.mul_sum]
  rw [hcards]

/-- Every edge lies either inside the cycle, inside its complement, or
crosses between the two sets.  This is the exact edge-count identity used
to turn the exterior estimate into Claim (c). -/
theorem edge_count_cycle_decomposition (C : CycleWitness K) :
    K.edgeFinset.card =
      (K.induce (↑C.vertexFinset : Set V)).edgeFinset.card +
      ((K.induce
          (↑(Finset.univ \ C.vertexFinset) : Set V)).edgeFinset.card +
        (edgesBetween K (Finset.univ \ C.vertexFinset)
          C.vertexFinset).card) := by
  classical
  let I : Finset (Sym2 V) :=
    {e ∈ K.edgeFinset | e.toFinset ⊆ C.vertexFinset}
  let O : Finset (Sym2 V) :=
    {e ∈ K.edgeFinset |
      e.toFinset ⊆ Finset.univ \ C.vertexFinset}
  let B : Finset (Sym2 V) :=
    edgesBetween K (Finset.univ \ C.vertexFinset) C.vertexFinset
  have hpart : K.edgeFinset = I ∪ O ∪ B := by
    ext e
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
          by_cases hxC : x ∈ C.vertexFinset
          · by_cases hyC : y ∈ C.vertexFinset
            · apply Finset.mem_union_left
              apply Finset.mem_union_left
              apply Finset.mem_filter.mpr
              refine ⟨he, ?_⟩
              intro z hz
              have hz' : z = x ∨ z = y := by simpa using hz
              rcases hz' with rfl | rfl
              · exact hxC
              · exact hyC
            · apply Finset.mem_union_right
              unfold B edgesBetween
              apply Finset.mem_filter.mpr
              refine ⟨he, y, ?_, x, hxC, ?_⟩
              · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyC⟩
              · exact Sym2.eq_swap
          · by_cases hyC : y ∈ C.vertexFinset
            · apply Finset.mem_union_right
              unfold B edgesBetween
              apply Finset.mem_filter.mpr
              refine ⟨he, x, ?_, y, hyC, rfl⟩
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxC⟩
            · apply Finset.mem_union_left
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨he, ?_⟩
              intro z hz
              have hz' : z = x ∨ z = y := by simpa using hz
              rcases hz' with rfl | rfl
              · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxC⟩
              · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyC⟩
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
        have hxI : x ∈ C.vertexFinset := hI (by simp)
        have hxO : x ∈ Finset.univ \ C.vertexFinset := hO (by simp)
        exact (Finset.mem_sdiff.mp hxO).2 hxI
  have hIB : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro e heI heB
    have hI := (Finset.mem_filter.mp heI).2
    unfold B edgesBetween at heB
    obtain ⟨heK, x, hxO, y, hyC, hxy⟩ := Finset.mem_filter.mp heB
    have hxI : x ∈ C.vertexFinset := by
      apply hI
      rw [hxy]
      simp
    exact (Finset.mem_sdiff.mp hxO).2 hxI
  have hOB : Disjoint O B := by
    apply Finset.disjoint_left.mpr
    intro e heO heB
    have hO := (Finset.mem_filter.mp heO).2
    unfold B edgesBetween at heB
    obtain ⟨heK, x, hxO, y, hyC, hxy⟩ := Finset.mem_filter.mp heB
    have hyO : y ∈ Finset.univ \ C.vertexFinset := by
      apply hO
      rw [hxy]
      simp
    exact (Finset.mem_sdiff.mp hyO).2 hyC
  have hIOB : Disjoint (I ∪ O) B :=
    Finset.disjoint_union_left.mpr ⟨hIB, hOB⟩
  rw [hpart, Finset.card_union_of_disjoint hIOB,
    Finset.card_union_of_disjoint hIO]
  unfold I O B
  rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset,
    SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  omega

/-- Full numerical conclusion of `claim:switching-terminal` for a terminal
graph, now including all edges of the graph rather than only exterior
incidences. -/
theorem switching_terminal_full_edge_bound (lit : LiteratureTheorems.{u})
    (C : CycleWitness K) (hlt : C.length < Fintype.card V)
    (hterminal : IsSwitchingTerminal K C) :
    ∃ j : (K.induce
        (↑(Finset.univ \ C.vertexFinset) : Set V)).ConnectedComponent,
      (∀ i, componentWeight C i ≤ componentWeight C j) ∧
      K.edgeFinset.card ≤
        (K.induce (↑C.vertexFinset : Set V)).edgeFinset.card +
          componentWeight C j * (Fintype.card V - C.length) / 2 := by
  obtain ⟨j, hmax, hbound⟩ :=
    switching_terminal_exterior_bound lit C hlt hterminal
  refine ⟨j, hmax, ?_⟩
  rw [edge_count_cycle_decomposition C]
  exact Nat.add_le_add_left hbound _

/-- Claim `claim:switching-terminal` assembled from finite descent and the
component estimate.  The chosen component `j` carries the paper's values
`ell` and `q` through `componentLongestPathLength` and
`componentAttachmentCount`. -/
theorem switching_terminal_claim_of_literature
    (lit : LiteratureTheorems.{u})
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (C : CycleWitness H) (h2c : IsTwoConnected H)
    (hloc : IsLocallyMaximalCycle C)
    (hlt : C.length < Fintype.card V) :
    ∃ (K : SimpleGraph V) (CK : CycleWitness K),
      SameCycle C CK ∧ IsTwoConnected K ∧ IsLocallyMaximalCycle CK ∧
      K.induce (↑C.vertexFinset : Set V) =
        H.induce (↑C.vertexFinset : Set V) ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      IsSwitchingTerminal K CK ∧
      ∃ j : (K.induce
          (↑(Finset.univ \ CK.vertexFinset) : Set V)).ConnectedComponent,
        (∀ i, componentWeight CK i ≤ componentWeight CK j) ∧
        K.edgeFinset.card ≤
          (K.induce (↑CK.vertexFinset : Set V)).edgeFinset.card +
            componentWeight CK j * (Fintype.card V - CK.length) / 2 := by
  classical
  obtain ⟨K, CK, hsame, hK2c, hKloc, hcore, hedges, hterminal⟩ :=
    switching_terminal_structure_of_literature lit H C h2c hloc
  have hlength : C.length = CK.length := by
    simpa [CycleWitness.length] using congrArg List.length hsame.2.2
  have hltK : CK.length < Fintype.card V := by omega
  obtain ⟨j, hmax, hbound⟩ :=
    switching_terminal_full_edge_bound lit CK hltK hterminal
  exact ⟨K, CK, hsame, hK2c, hKloc, hcore, hedges, hterminal,
    j, hmax, hbound⟩

end

end Erdos767
