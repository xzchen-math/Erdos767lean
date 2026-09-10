import Erdos767.Chapter5RouteA

/-!
# Arithmetic for the base-range minimal-counterexample argument

These lemmas isolate the two pieces of integer arithmetic used in the proof
of manuscript Lemma `lem:base`: the one-vertex increment of `h`, and the
binary merging estimate on the `t`-branch.
-/

namespace Erdos767

/-- A small complete graph is bounded by the corresponding `t` value. -/
theorem choose_two_le_t {k m : ℕ} (hm : m ≤ k + 1) :
    m.choose 2 ≤ t k m := by
  rw [Nat.choose_two_right]
  unfold t
  apply Nat.div_le_div_right
  have hmul := Nat.mul_le_mul_left m (show m - 1 ≤ k + 1 by omega)
  simpa [Nat.mul_comm] using hmul

/-- For an overlapping separator, a small side can be charged only for its
vertices other than the common cut vertex. -/
theorem choose_two_le_half_mul_sub_one {k m : ℕ}
    (hm0 : 1 ≤ m) (hm : m ≤ k + 1) :
    m.choose 2 ≤ ((k + 1) * (m - 1)) / 2 := by
  rw [Nat.choose_two_right]
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right (m - 1) hm

/-- Two floor-linear terms merge without loss. -/
theorem t_add_le_t_add {k x y : ℕ} :
    t k x + t k y ≤ t k (x + y) := by
  unfold t
  rw [Nat.mul_add]
  exact Nat.add_div_le_add_div _ _ _

/-- The `t`-branch estimate for two induced pieces with no common vertex. -/
theorem h_add_le_t_of_t_branch_disjoint {k n x y : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hxy : x + y = n) (hx : x < n) (hy : y < n)
    (hpt : p k n ≤ t k n) :
    h k x + h k y ≤ t k n := by
  have hxle : x ≤ n := by omega
  have hyle : y ≤ n := by omega
  have hbound (m : ℕ) (hmn : m ≤ n) : h k m ≤ t k m := by
    by_cases hm : m ≤ k + 1
    · simp [h, hm]
      exact choose_two_le_t hm
    · have hmLarge : k + 2 ≤ m := by omega
      have heq := h_eq_t_descends hk hmLarge hmn (by
        rw [h_eq_max hn, max_eq_left hpt])
      exact le_of_eq heq
  have hxBound := hbound x hxle
  have hyBound := hbound y hyle
  calc
    h k x + h k y ≤ t k x + t k y := Nat.add_le_add hxBound hyBound
    _ ≤ t k (x + y) := t_add_le_t_add
    _ = t k n := by rw [hxy]

/-- The `t`-branch estimate for two pieces meeting in one cut vertex. -/
theorem h_add_le_t_of_t_branch_cut {k n x y : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hxy : x + y - 1 = n) (hx0 : 1 ≤ x) (hy0 : 1 ≤ y)
    (hx : x < n) (hy : y < n) (hpt : p k n ≤ t k n) :
    h k x + h k y ≤ t k n := by
  have hnUpper : n ≤ 2 * k + 2 :=
    le_two_mul_add_two_of_p_le_t hk hn hpt
  have hxle : x ≤ n := by omega
  have hyle : y ≤ n := by omega
  have hnotBoth : x ≤ k + 1 ∨ y ≤ k + 1 := by omega
  by_cases hxSmall : x ≤ k + 1
  · have hxH : h k x = x.choose 2 := by simp [h, hxSmall]
    have hxCharge := choose_two_le_half_mul_sub_one hx0 hxSmall
    by_cases hySmall' : y ≤ k + 1
    · have hyH : h k y = y.choose 2 := by simp [h, hySmall']
      have hyCharge := choose_two_le_half_mul_sub_one hy0 hySmall'
      rw [hxH, hyH]
      have hadd := Nat.add_le_add hxCharge hyCharge
      have hfloor := Nat.add_div_le_add_div
        ((k + 1) * (x - 1)) ((k + 1) * (y - 1)) 2
      have hparts : (x - 1) + (y - 1) = n - 1 := by omega
      calc
        x.choose 2 + y.choose 2 ≤
            ((k + 1) * (x - 1)) / 2 +
              ((k + 1) * (y - 1)) / 2 := hadd
        _ ≤ (((k + 1) * (x - 1)) +
              ((k + 1) * (y - 1))) / 2 := hfloor
        _ = t k (n - 1) := by rw [← Nat.mul_add, hparts]; rfl
        _ ≤ t k n := by
          unfold t
          exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
    · have hyLarge : k + 2 ≤ y := by omega
      have hyH := h_eq_t_descends hk hyLarge hyle (by
        rw [h_eq_max hn, max_eq_left hpt])
      rw [hxH, hyH]
      have hparts : (x - 1) + y = n := by omega
      calc
        x.choose 2 + t k y ≤
            ((k + 1) * (x - 1)) / 2 + t k y :=
          Nat.add_le_add_right hxCharge _
        _ ≤ (((k + 1) * (x - 1)) + (k + 1) * y) / 2 := by
          unfold t
          exact Nat.add_div_le_add_div _ _ _
        _ = t k n := by rw [← Nat.mul_add, hparts]; rfl
  · have hySmall : y ≤ k + 1 := hnotBoth.resolve_left hxSmall
    have hyH : h k y = y.choose 2 := by simp [h, hySmall]
    have hyCharge := choose_two_le_half_mul_sub_one hy0 hySmall
    have hxLarge : k + 2 ≤ x := by omega
    have hxH := h_eq_t_descends hk hxLarge hxle (by
      rw [h_eq_max hn, max_eq_left hpt])
    rw [hxH, hyH]
    have hparts : x + (y - 1) = n := by omega
    calc
      t k x + y.choose 2 ≤
          t k x + ((k + 1) * (y - 1)) / 2 :=
        Nat.add_le_add_left hyCharge _
      _ ≤ ((k + 1) * x + (k + 1) * (y - 1)) / 2 := by
        unfold t
        exact Nat.add_div_le_add_div _ _ _
      _ = t k n := by rw [← Nat.mul_add, hparts]; rfl

/-- The floor-linear branch grows by at least `floor ((k+1)/2)` when
the order grows by one. -/
theorem t_increment_lower {k m : ℕ} :
    t k m + (k + 1) / 2 ≤ t k (m + 1) := by
  unfold t
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.add_div_le_add_div _ _ _

/-- The increment used to obtain the minimum-degree bound in a minimal
counterexample. -/
theorem h_increment_lower {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n) :
    h k (n - 1) + ((k + 1) / 2 + 1) ≤ h k n + 1 := by
  have hnPrev : n - 1 + 1 = n := by omega
  by_cases hboundary : n - 1 ≤ k + 1
  · have hprevChoose : h k (n - 1) = (n - 1).choose 2 := by
      simp [h, hboundary]
    have hprevT : h k (n - 1) ≤ t k (n - 1) := by
      rw [hprevChoose]
      exact choose_two_le_t hboundary
    have htInc := t_increment_lower (k := k) (m := n - 1)
    rw [hnPrev] at htInc
    have htH := t_le_h (k := k) (n := n) hn
    omega
  · have hprevLarge : k + 2 ≤ n - 1 := by omega
    by_cases hpt : p k n ≤ t k n
    · have hnH : h k n = t k n := by
        rw [h_eq_max hn, max_eq_left hpt]
      have hprevH := h_eq_t_descends hk hprevLarge (by omega) hnH
      rw [hnH, hprevH]
      have htInc := t_increment_lower (k := k) (m := n - 1)
      rw [hnPrev] at htInc
      omega
    · have htp : t k n < p k n := by omega
      have hnH : h k n = p k n := by
        rw [h_eq_max hn, max_eq_right (by omega)]
      by_cases hprevP : t k (n - 1) ≤ p k (n - 1)
      · have hprevH : h k (n - 1) = p k (n - 1) := by
          rw [h_eq_max hprevLarge, max_eq_right hprevP]
        obtain ⟨a, haA, hpa⟩ := exists_maximizing_splitTerm k (n - 1)
        have haBounds := mem_A_iff.mp haA
        have hinc := p_succ_ge_of_eq_splitTerm haA (by omega) hpa
        rw [hnPrev] at hinc
        rw [hnH, hprevH]
        omega
      · have hprevT : p k (n - 1) < t k (n - 1) := by omega
        have hprevH : h k (n - 1) = t k (n - 1) := by
          rw [h_eq_max hprevLarge, max_eq_left (by omega)]
        rw [hnH, hprevH]
        have hpStep : t k n + 1 ≤ p k n := by omega
        have htInc := t_increment_lower (k := k) (m := n - 1)
        rw [hnPrev] at htInc
        omega

end Erdos767
