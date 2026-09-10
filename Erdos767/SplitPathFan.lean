import Erdos767.Constructions

/-!
# The split construction is path-fan-free

This file closes the remaining construction gap in Section 3.  The key
combinatorial fact is that a path in a graph whose right side is independent
uses at most one more right-side vertex than left-side vertices.  For a
left-side center in the split construction, the path avoids one of the `a`
left vertices; hence it uses at most `a` right vertices.  Its remaining
neighbors of the center lie in the cyclic core and number at most
`k + 1 - a`.
-/

namespace Erdos767

open SimpleGraph

namespace SplitPath

@[simp] def isLeft {A B : Type*} : A ⊕ B → Bool
  | .inl _ => true
  | .inr _ => false

@[simp] def isRight {A B : Type*} : A ⊕ B → Bool
  | .inl _ => false
  | .inr _ => true

def walkLeftVertices {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} {u v : A ⊕ B}
    (pth : G.Walk u v) : Finset (A ⊕ B) :=
  pth.support.toFinset.filter (fun z ↦ isLeft z = true)

def walkRightVertices {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} {u v : A ⊕ B}
    (pth : G.Walk u v) : Finset (A ⊕ B) :=
  pth.support.toFinset.filter (fun z ↦ isRight z = true)

theorem walk_side_count_aux
    {A B : Type*} {G : SimpleGraph (A ⊕ B)}
    (hRight : ∀ y y' : B, ¬ G.Adj (.inr y) (.inr y'))
    {u v : A ⊕ B} (pth : G.Walk u v) :
    match u with
    | .inl _ => (pth.support.filter isRight).length ≤
        (pth.support.filter isLeft).length
    | .inr _ => (pth.support.filter isRight).length ≤
        (pth.support.filter isLeft).length + 1 := by
  induction pth with
  | @nil u =>
      cases u <;> simp [List.filter, isLeft, isRight]
  | @cons u u' v hadj pth ih =>
      cases u with
      | inl x =>
          cases u' with
          | inl x' =>
              simp [List.filter, isLeft, isRight] at ih ⊢
              omega
          | inr y' =>
              simp [List.filter, isLeft, isRight] at ih ⊢
              omega
      | inr y =>
          cases u' with
          | inl x' =>
              simp [List.filter, isLeft, isRight] at ih ⊢
              omega
          | inr y' =>
              exact (hRight y y' hadj).elim

theorem walk_side_count
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)}
    (hRight : ∀ y y' : B, ¬ G.Adj (.inr y) (.inr y'))
    {u v : A ⊕ B} (pth : G.Walk u v) (hp : pth.IsPath) :
    match u with
    | .inl _ => (walkRightVertices pth).card ≤ (walkLeftVertices pth).card
    | .inr _ => (walkRightVertices pth).card ≤
        (walkLeftVertices pth).card + 1 := by
  have hleft : (walkLeftVertices pth).card =
      (pth.support.filter isLeft).length := by
    rw [walkLeftVertices, ← pth.support.toFinset_filter isLeft]
    exact List.toFinset_card_of_nodup (hp.support_nodup.filter isLeft)
  have hright : (walkRightVertices pth).card =
      (pth.support.filter isRight).length := by
    rw [walkRightVertices, ← pth.support.toFinset_filter isRight]
    exact List.toFinset_card_of_nodup (hp.support_nodup.filter isRight)
  cases u <;> simp only at hleft hright ⊢ <;>
    rw [hleft, hright] <;>
    exact walk_side_count_aux hRight pth

def walkLeftNeighbors {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} [DecidableRel G.Adj]
    (x : A ⊕ B) {u v : A ⊕ B} (pth : G.Walk u v) : Finset (A ⊕ B) :=
  (walkNeighbors x pth).filter (fun z ↦ isLeft z = true)

def walkRightNeighbors {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} [DecidableRel G.Adj]
    (x : A ⊕ B) {u v : A ⊕ B} (pth : G.Walk u v) : Finset (A ⊕ B) :=
  (walkNeighbors x pth).filter (fun z ↦ isRight z = true)

theorem card_walkNeighbors_eq_side_sum
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} [DecidableRel G.Adj]
    (x : A ⊕ B) {u v : A ⊕ B} (pth : G.Walk u v) :
    (walkNeighbors x pth).card =
      (walkLeftNeighbors x pth).card + (walkRightNeighbors x pth).card := by
  have hu : walkLeftNeighbors x pth ∪ walkRightNeighbors x pth =
      walkNeighbors x pth := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hzL | hzR
      · exact (Finset.mem_filter.mp hzL).1
      · exact (Finset.mem_filter.mp hzR).1
    · intro hz
      cases z with
      | inl z =>
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨hz, rfl⟩
      | inr z =>
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hd : Disjoint (walkLeftNeighbors x pth) (walkRightNeighbors x pth) := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    have hl := (Finset.mem_filter.mp hzL).2
    have hr := (Finset.mem_filter.mp hzR).2
    cases z <;> simp [isLeft, isRight] at hl hr
  rw [← hu, Finset.card_union_of_disjoint hd]

theorem walkRightNeighbors_subset_walkRightVertices
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} [DecidableRel G.Adj]
    (x : A ⊕ B) {u v : A ⊕ B} (pth : G.Walk u v) :
    walkRightNeighbors x pth ⊆ walkRightVertices pth := by
  intro z hz
  have hzn : z ∈ walkNeighbors x pth := (Finset.mem_filter.mp hz).1
  have hzs : z ∈ pth.support.toFinset := (Finset.mem_filter.mp hzn).1
  exact Finset.mem_filter.mpr ⟨hzs, (Finset.mem_filter.mp hz).2⟩

theorem walkLeftVertices_card_le_sub_one
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)} {x : A} {u v : A ⊕ B}
    (pth : G.Walk u v) (hx : (Sum.inl x : A ⊕ B) ∉ pth.support) :
    (walkLeftVertices pth).card ≤ Fintype.card A - 1 := by
  let U : Finset (A ⊕ B) := Finset.univ.map Function.Embedding.inl
  have hsub : walkLeftVertices pth ⊆ U.erase (.inl x) := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    apply Finset.mem_erase.mpr
    constructor
    · intro hzx
      subst z
      exact hx (by simpa [walkLeftVertices] using hz'.1)
    · cases z with
      | inl z => simp [U]
      | inr z => simp [isLeft] at hz'
  calc
    (walkLeftVertices pth).card ≤ (U.erase (.inl x)).card :=
      Finset.card_le_card hsub
    _ = U.card - 1 := Finset.card_erase_of_mem (by simp [U])
    _ = Fintype.card A - 1 := by simp [U]

theorem walkRightVertices_card_le_left_add_one
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph (A ⊕ B)}
    (hRight : ∀ y y' : B, ¬ G.Adj (.inr y) (.inr y'))
    {u v : A ⊕ B} (pth : G.Walk u v) (hp : pth.IsPath) :
    (walkRightVertices pth).card ≤ (walkLeftVertices pth).card + 1 := by
  have h := walk_side_count hRight pth hp
  cases u <;> simp only at h ⊢ <;> omega

theorem split_walkLeftNeighbors_card_le
    {k n a : ℕ} [NeZero a] (ha2 : 2 ≤ a) (x : Fin a)
    {u v : Fin a ⊕ Fin (n - a)} (pth : (splitGraph k n a).Walk u v) :
    (walkLeftNeighbors (.inl x) pth).card ≤ k + 1 - a := by
  let F : Finset (Fin a ⊕ Fin (n - a)) :=
    ((cyclicDegreeGraph (k + 1 - a) a).neighborFinset x).map
      Function.Embedding.inl
  have hsub : walkLeftNeighbors (.inl x) pth ⊆ F := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    cases z with
    | inl z =>
        apply Finset.mem_map.mpr
        refine ⟨z, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact splitGraph_adj_left.mp (Finset.mem_filter.mp hz'.1).2
    | inr z => simp [isLeft] at hz'
  calc
    (walkLeftNeighbors (.inl x) pth).card ≤ F.card := Finset.card_le_card hsub
    _ = (cyclicDegreeGraph (k + 1 - a) a).degree x := by
      simp [F, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ k + 1 - a := cyclicDegreeGraph_degree_le (k + 1 - a) a ha2 x

/-- The path-alternation proof for the split lower-bound construction. -/
theorem splitGraph_pathFanFree_aux
    (k n a : ℕ) [NeZero a] (hk : 1 ≤ k) (ha : a ∈ A k) :
    PathFanFree (splitGraph k n a) (k + 2) := by
  intro hfan
  rcases hfan with ⟨x, u, v, pth, hp, hx, hcount⟩
  have haBounds := mem_A_iff.mp ha
  have ha2 : 2 ≤ a := by omega
  cases x with
  | inr y =>
      have hdeg := card_walkNeighbors_le_degree (G := splitGraph k n a)
        (x := (.inr y)) pth
      rw [splitGraph_degree_right] at hdeg
      omega
  | inl x =>
      have hrightGraph : ∀ y y' : Fin (n - a),
          ¬(splitGraph k n a).Adj (.inr y) (.inr y') := by
        intro y y'
        exact splitGraph_adj_right
      have hleftSupport : (walkLeftVertices pth).card ≤ a - 1 := by
        simpa using walkLeftVertices_card_le_sub_one pth hx
      have hrightSupport :=
        walkRightVertices_card_le_left_add_one hrightGraph pth hp
      have hrightNeighbors : (walkRightNeighbors (.inl x) pth).card ≤ a := by
        calc
          _ ≤ (walkRightVertices pth).card :=
            Finset.card_le_card (walkRightNeighbors_subset_walkRightVertices _ _)
          _ ≤ (walkLeftVertices pth).card + 1 := hrightSupport
          _ ≤ a := by omega
      have hleftNeighbors := split_walkLeftNeighbors_card_le ha2 x pth
      rw [card_walkNeighbors_eq_side_sum] at hcount
      omega

end SplitPath

/-- The split construction from Section 3 contains no `PF_(k+2)`. -/
theorem splitGraph_pathFanFree
    (k n a : ℕ) [NeZero a] (hk : 1 ≤ k) (ha : a ∈ A k) :
    PathFanFree (splitGraph k n a) (k + 2) :=
  SplitPath.splitGraph_pathFanFree_aux k n a hk ha

end Erdos767
