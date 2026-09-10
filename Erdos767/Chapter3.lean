import Erdos767.Arithmetic
import Erdos767.Constructions

/-!
# All formal statements from Section 3

This file collects the manuscript-facing theorems from Section 3,
“Extremal constructions and arithmetic”.  Square-root cutoffs are also given
below in an equivalent integer form, which is substantially easier to reuse in
later graph-theoretic files.
-/

namespace Erdos767

/-- The irrational cutoff occurring in Lemmas `lem:linear-bound` and
`lem:B-equals-f`. -/
noncomputable def realCutoff (k : ℕ) : ℝ :=
  (1 + Real.sqrt 3 / 2) * (k + 1)

private theorem square_le_of_le_floor_realCutoff {k n : ℕ}
    (hKn : k + 1 ≤ n) (hn : n ≤ Nat.floor (realCutoff k)) :
    4 * (n - (k + 1)) ^ 2 ≤ 3 * (k + 1) ^ 2 := by
  have hcutNonneg : 0 ≤ realCutoff k := by
    unfold realCutoff
    positivity
  have hnR : (n : ℝ) ≤ realCutoff k := by
    have hnFloorR : (n : ℝ) ≤ (Nat.floor (realCutoff k) : ℝ) := by
      exact_mod_cast hn
    exact hnFloorR.trans (Nat.floor_le hcutNonneg)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg 3
  have hd0 : (0 : ℝ) ≤ (n : ℝ) - (k + 1) := by
    have hKnR : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hKn
    norm_num at hKnR
    linarith
  have hlin :
      2 * ((n : ℝ) - (k + 1)) ≤ Real.sqrt 3 * (k + 1) := by
    unfold realCutoff at hnR
    nlinarith
  have hsquareR :
      4 * ((n : ℝ) - (k + 1)) ^ 2 ≤ 3 * ((k : ℝ) + 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlin)
      (add_nonneg (mul_nonneg hs0 (by positivity)) hd0)]
  have hsubCast : ((n - (k + 1) : ℕ) : ℝ) = (n : ℝ) - (k + 1) := by
    rw [Nat.cast_sub hKn]
    norm_num
  rw [← hsubCast] at hsquareR
  exact_mod_cast hsquareR

/-- Upper-bound API for the finite maximum defining `p_k(n)`. -/
theorem p_le_of_forall_splitTerm_le {k n B : ℕ}
    (hB : ∀ a ∈ A k, splitTerm k n a ≤ B) :
    p k n ≤ B := by
  exact Finset.sup_le hB

/-- Lemma `lem:S-terminal`, expressed with the equivalent integer threshold
`5k+1 ≤ 2n`. -/
theorem p_eq_terminal_of_five_mul_add_one_le_two_mul
    {k n : ℕ} (hk : 2 ≤ k) (hn : 5 * k + 1 ≤ 2 * n) :
    p k n = (k + 1) * (n - k - 1) := by
  apply Nat.le_antisymm
  · apply p_le_of_forall_splitTerm_le
    intro a ha
    have haBounds := mem_A_iff.mp ha
    have haK : a ≤ k + 1 := haBounds.2
    have hKn : k + 1 ≤ n := by omega
    let d := k + 1 - a
    have had : a + d = k + 1 := by
      dsimp [d]
      omega
    by_cases hd0 : d = 0
    · have haeq : a = k + 1 := by omega
      subst a
      simp [splitTerm]
      omega
    by_cases hd1 : d = 1
    · have haeq : a = k := by omega
      subst a
      have hnStrong : 2 * k + 1 + k / 2 ≤ n :=
        terminal_d_one_nonnegative hn
      have hsubk : n - k = (n - k - 1) + 1 := by omega
      have hdk : k + 1 - k = 1 := by omega
      rw [splitTerm, hdk]
      simp only [Nat.mul_one]
      have hr : k + k / 2 ≤ n - k - 1 := by omega
      calc
        k * (n - k) + k / 2
            = k * ((n - k - 1) + 1) + k / 2 :=
              congrArg (fun x : ℕ => k * x + k / 2) hsubk
        _ = k * (n - k - 1) + (k + k / 2) := by
          rw [Nat.mul_add]
          omega
        _ ≤ k * (n - k - 1) + (n - k - 1) := Nat.add_le_add_left hr _
        _ = (k + 1) * (n - k - 1) := by
          rw [Nat.add_mul]
          simp
    · have hd2 : 2 ≤ d := by omega
      have hdn : d ≤ k + 1 := by omega
      have h3a : 3 * a ≤ 2 * (n - (k + 1)) := by
        omega
      have hmul : 3 * a * d ≤ 2 * (n - (k + 1)) * d := by
        exact Nat.mul_le_mul_right d h3a
      have hsubA : n - a = (n - (k + 1)) + d := by omega
      have hsubK : n - k - 1 = n - (k + 1) := by omega
      have htwoDiv : 2 * ((a * d) / 2) ≤ a * d := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self (a * d) 2
      rw [splitTerm, show k + 1 - a = d by rfl, hsubA, hsubK]
      have hdouble :
          2 * (a * ((n - (k + 1)) + d) + a * d / 2) ≤
            2 * ((k + 1) * (n - (k + 1))) := by
        calc
          2 * (a * ((n - (k + 1)) + d) + a * d / 2)
              = 2 * (a * ((n - (k + 1)) + d)) + 2 * (a * d / 2) := by
                omega
          _ ≤ 2 * (a * ((n - (k + 1)) + d)) + a * d := by omega
          _ = 2 * a * (n - (k + 1)) + 3 * a * d := by ring
          _ ≤ 2 * a * (n - (k + 1)) + 2 * (n - (k + 1)) * d := by
            omega
          _ = 2 * ((a + d) * (n - (k + 1))) := by ring
          _ = 2 * ((k + 1) * (n - (k + 1))) := by rw [had]
      omega
  · simpa [Nat.sub_sub] using p_ge_terminal k n

/-- Lemma `lem:S-terminal` with the natural-number spelling of
`n ≥ ceil((5k+1)/2)`. -/
theorem p_eq_terminal {k n : ℕ} (hk : 2 ≤ k)
    (hn : (5 * k + 2) / 2 ≤ n) :
    p k n = (k + 1) * (n - k - 1) := by
  apply p_eq_terminal_of_five_mul_add_one_le_two_mul hk
  omega

/-- Terminal branch of Lemma `lem:B-equals-f`. -/
theorem h_eq_terminal {k n : ℕ} (hk : 2 ≤ k)
    (hn : (5 * k + 2) / 2 ≤ n) :
    h k n = (k + 1) * (n - k - 1) := by
  have hkn : k + 2 ≤ n := by omega
  rw [h_eq_max hkn, p_eq_terminal hk hn]
  apply max_eq_right
  unfold t
  have hnr : n ≤ 2 * (n - k - 1) := by omega
  have hlin : (k + 1) * n ≤ (k + 1) * (2 * (n - k - 1)) :=
    Nat.mul_le_mul_left (k + 1) hnr
  calc
    ((k + 1) * n) / 2
        ≤ ((k + 1) * (2 * (n - k - 1))) / 2 :=
          Nat.div_le_div_right hlin
    _ = (2 * ((k + 1) * (n - k - 1))) / 2 := by
      congr 1
      ac_rfl
    _ = (k + 1) * (n - k - 1) := by omega

/-- Rewrite a split term as the integer part of its concave quadratic. -/
theorem splitTerm_eq_quadratic_div_two {k n a : ℕ}
    (haK : a ≤ k + 1) (hKn : k + 1 ≤ n) :
    splitTerm k n a =
      (a * (2 * n + (k + 1) - 3 * a)) / 2 := by
  have han : a ≤ n := haK.trans hKn
  have h3a : 3 * a ≤ 2 * n + (k + 1) := by omega
  have hnum :
      a * (k + 1 - a) + 2 * (a * (n - a)) =
        a * (2 * n + (k + 1) - 3 * a) := by
    nlinarith [Nat.sub_add_cancel haK, Nat.sub_add_cancel han,
      Nat.sub_add_cancel h3a]
  calc
    splitTerm k n a = a * (n - a) + (a * (k + 1 - a)) / 2 := rfl
    _ = (a * (k + 1 - a) + 2 * (a * (n - a))) / 2 := by
      rw [Nat.add_mul_div_left (a * (k + 1 - a)) (a * (n - a)) (by omega)]
      omega
    _ = (a * (2 * n + (k + 1) - 3 * a)) / 2 := by rw [hnum]

/-- Every split term lies below the vertex of the associated real parabola,
with denominators cleared. -/
theorem twentyFour_mul_splitTerm_le_square {k n a : ℕ}
    (haK : a ≤ k + 1) (hKn : k + 1 ≤ n) :
    24 * splitTerm k n a ≤ (2 * n + (k + 1)) ^ 2 := by
  have han : a ≤ n := haK.trans hKn
  have hfloor : 2 * ((a * (k + 1 - a)) / 2) ≤ a * (k + 1 - a) := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (a * (k + 1 - a)) 2
  have hdouble :
      2 * splitTerm k n a ≤
        2 * (a * (n - a)) + a * (k + 1 - a) := by
    unfold splitTerm
    omega
  have hpolyZ :
      (12 : ℤ) *
          (2 * (a : ℤ) * ((n : ℤ) - a) +
            (a : ℤ) * (((k + 1 : ℕ) : ℤ) - a)) ≤
        (2 * (n : ℤ) + ((k + 1 : ℕ) : ℤ)) ^ 2 := by
    nlinarith [sq_nonneg
      (2 * (n : ℤ) + ((k + 1 : ℕ) : ℤ) - 6 * (a : ℤ))]
  have hpoly :
      12 * (2 * a * (n - a) + a * (k + 1 - a)) ≤
        (2 * n + (k + 1)) ^ 2 := by
    exact_mod_cast hpolyZ
  nlinarith [Nat.mul_le_mul_left 12 hdouble]

theorem splitTerm_le_middle_square {k n a : ℕ}
    (haK : a ≤ k + 1) (hKn : k + 1 ≤ n) :
    splitTerm k n a ≤ (2 * n + (k + 1)) ^ 2 / 24 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 24)).mpr
  simpa [Nat.mul_comm] using twentyFour_mul_splitTerm_le_square haK hKn

/-- The rounding identity underlying the middle branch of
`lem:B-equals-f`. -/
private theorem rounded_quadratic_identity (S : ℕ) :
    let a := (S + 3) / 6
    (a * (S - 3 * a)) / 2 = S ^ 2 / 24 := by
  dsimp
  let a := (S + 3) / 6
  let P := a * (S - 3 * a)
  let X := P / 2
  have haLo : 6 * a ≤ S + 3 := by
    have ha : a ≤ (S + 3) / 6 := by rfl
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 6)).mp ha
  have haHi : S + 3 < 6 * (a + 1) := by
    have ha : (S + 3) / 6 < a + 1 := by simp only [a]; omega
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 6)).mp ha
  have h3a : 3 * a ≤ S := by
    by_cases ha0 : a = 0
    · omega
    · omega
  have hXLo : X * 2 ≤ P := by
    simpa [X] using Nat.div_mul_le_self P 2
  have hXHi : P < (X + 1) * 2 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp
    simp [X]
  have hLoZ :
      (X : ℤ) * 24 ≤ (S : ℤ) ^ 2 := by
    have hXLoZ : (X : ℤ) * 2 ≤ (P : ℤ) := by exact_mod_cast hXLo
    have hPZ :
        (P : ℤ) = (a : ℤ) * ((S : ℤ) - 3 * (a : ℤ)) := by
      simp [P, Nat.cast_sub h3a]
    rw [hPZ] at hXLoZ
    nlinarith [sq_nonneg ((S : ℤ) - 6 * (a : ℤ))]
  have hHiZ :
      (S : ℤ) ^ 2 < ((X : ℤ) + 1) * 24 := by
    have hXHiZ :
        (P : ℤ) < ((X : ℤ) + 1) * 2 := by exact_mod_cast hXHi
    have hPZ :
        (P : ℤ) = (a : ℤ) * ((S : ℤ) - 3 * (a : ℤ)) := by
      simp [P, Nat.cast_sub h3a]
    have haLoZ : (6 : ℤ) * a ≤ S + 3 := by exact_mod_cast haLo
    have haHiZ : (S : ℤ) + 3 < 6 * ((a : ℤ) + 1) := by
      exact_mod_cast haHi
    have hleft : 0 ≤ (S : ℤ) - 6 * a + 3 := by omega
    have hright : 0 ≤ 3 - ((S : ℤ) - 6 * a) := by omega
    have hdelta : ((S : ℤ) - 6 * a) ^ 2 ≤ 9 := by
      nlinarith [mul_nonneg hleft hright]
    rw [hPZ] at hXHiZ
    nlinarith
  have hLo : X * 24 ≤ S ^ 2 := by exact_mod_cast hLoZ
  have hHi : S ^ 2 < (X + 1) * 24 := by exact_mod_cast hHiZ
  change X = S ^ 2 / 24
  exact (Nat.div_eq_of_lt_le hLo hHi).symm

/-- The first branch of Lemma `lem:B-equals-f`, with the irrational cutoff
replaced by its equivalent squared inequality. -/
theorem h_eq_t_of_square_le {k n : ℕ} (hn : k + 2 ≤ n)
    (hcut : 4 * (n - (k + 1)) ^ 2 ≤ 3 * (k + 1) ^ 2) :
    h k n = t k n := by
  have hKn : k + 1 ≤ n := by omega
  have hsquare : (2 * n + (k + 1)) ^ 2 ≤ 12 * ((k + 1) * n) := by
    have hsub : n - (k + 1) + (k + 1) = n := by omega
    nlinarith
  have hp : p k n ≤ t k n := by
    apply p_le_of_forall_splitTerm_le
    intro a ha
    have haK := (mem_A_iff.mp ha).2
    have h24 := twentyFour_mul_splitTerm_le_square haK hKn
    have h2 : 2 * splitTerm k n a ≤ (k + 1) * n := by
      nlinarith
    unfold t
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr (by
      simpa [Nat.mul_comm] using h2)
  rw [h_eq_max hn]
  exact max_eq_left hp

/-- The exact value of `p_k(n)` in the middle interval of
Lemma `lem:B-equals-f`.  The first hypothesis says that `n` lies strictly
above the first (square-root) cutoff, and the last says it lies below the
terminal cutoff. -/
theorem p_eq_middle {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hfirst : 3 * (k + 1) ^ 2 < 4 * (n - (k + 1)) ^ 2)
    (hterminal : n ≤ (5 * k + 2) / 2) :
    p k n = (2 * n + (k + 1)) ^ 2 / 24 := by
  let S := 2 * n + (k + 1)
  let a := (S + 3) / 6
  have hKn : k + 1 ≤ n := by omega
  have hd2 : 2 ≤ n - (k + 1) := by
    have hsub : n - (k + 1) + (k + 1) = n := by omega
    by_contra hd
    have : n - (k + 1) ≤ 1 := by omega
    nlinarith
  have hqLo : 2 * ((k + 1) / 2) ≤ k + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) 2
  have hqHi : k + 1 < 2 * ((k + 1) / 2 + 1) := by
    have hlt : (k + 1) / 2 < (k + 1) / 2 + 1 := by omega
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp hlt
  have haLower : (k + 1) / 2 + 1 ≤ a := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 6)).mpr
    dsimp [a, S]
    omega
  have haUpper : a ≤ k + 1 := by
    have hlt : S + 3 < (k + 2) * 6 := by
      dsimp [S]
      omega
    have haLt : a < k + 2 := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 6)).mpr
      simpa [Nat.mul_comm] using hlt
    omega
  have haA : a ∈ A k := mem_A_iff.mpr ⟨haLower, haUpper⟩
  apply Nat.le_antisymm
  · apply p_le_of_forall_splitTerm_le
    intro b hb
    exact splitTerm_le_middle_square (mem_A_iff.mp hb).2 hKn
  · have hge := p_ge_splitTerm (n := n) haA
    have hchosen : splitTerm k n a = S ^ 2 / 24 := by
      rw [splitTerm_eq_quadratic_div_two haUpper hKn]
      exact rounded_quadratic_identity S
    rw [hchosen] at hge
    simpa [S] using hge

/-- Middle branch of Lemma `lem:B-equals-f`. -/
theorem h_eq_middle {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (hfirst : 3 * (k + 1) ^ 2 < 4 * (n - (k + 1)) ^ 2)
    (hterminal : n ≤ (5 * k + 2) / 2) :
    h k n = (2 * n + (k + 1)) ^ 2 / 24 := by
  have hp := p_eq_middle hk hn hfirst hterminal
  have hKn : k + 1 ≤ n := by omega
  have hsub : n - (k + 1) + (k + 1) = n := by omega
  have h12 : 12 * ((k + 1) * n) < (2 * n + (k + 1)) ^ 2 := by
    nlinarith
  have ht24 : 24 * t k n ≤ 12 * ((k + 1) * n) := by
    unfold t
    have hfloor : 2 * (((k + 1) * n) / 2) ≤ (k + 1) * n := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * n) 2
    nlinarith
  have ht : t k n ≤ (2 * n + (k + 1)) ^ 2 / 24 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 24)).mpr
    simpa [Nat.mul_comm] using le_trans ht24 (Nat.le_of_lt h12)
  rw [h_eq_max hn, hp]
  exact max_eq_right ht

/-- Lemma `lem:B-equals-f` in a kernel-friendly piecewise form.  Its first
test is precisely the square of the manuscript's first irrational cutoff. -/
theorem h_eq_piecewise_discrete {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n) :
    h k n =
      if (5 * k + 2) / 2 ≤ n then
        (k + 1) * (n - k - 1)
      else if 4 * (n - (k + 1)) ^ 2 ≤ 3 * (k + 1) ^ 2 then
        t k n
      else
        (2 * n + (k + 1)) ^ 2 / 24 := by
  by_cases hterm : (5 * k + 2) / 2 ≤ n
  · simp only [hterm, if_true]
    exact h_eq_terminal hk hterm
  · simp only [hterm, if_false]
    by_cases hcut : 4 * (n - (k + 1)) ^ 2 ≤ 3 * (k + 1) ^ 2
    · simp only [hcut, if_true]
      exact h_eq_t_of_square_le hn hcut
    · simp only [hcut, if_false]
      apply h_eq_middle hk hn
      · omega
      · omega

/-- First branch of Lemma `lem:B-equals-f` with the manuscript's real
cutoff. -/
theorem h_eq_t_of_le_floor_realCutoff {k n : ℕ} (hn : k + 2 ≤ n)
    (hcut : n ≤ Nat.floor (realCutoff k)) :
    h k n = t k n := by
  exact h_eq_t_of_square_le hn
    (square_le_of_le_floor_realCutoff (by omega) hcut)

/-- Middle branch of Lemma `lem:B-equals-f` with the manuscript's real
cutoff. -/
theorem h_eq_middle_of_floor_realCutoff_lt {k n : ℕ} (hk : 2 ≤ k)
    (hn : k + 2 ≤ n) (hcut : Nat.floor (realCutoff k) < n)
    (hterminal : n < (5 * k + 2) / 2) :
    h k n = (2 * n + (k + 1)) ^ 2 / 24 := by
  have hcutNonneg : 0 ≤ realCutoff k := by
    unfold realCutoff
    positivity
  have hnR : realCutoff k < (n : ℝ) :=
    (Nat.floor_lt hcutNonneg).mp hcut
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg 3
  have hKn : k + 1 ≤ n := by omega
  have hd0 : (0 : ℝ) ≤ (n : ℝ) - ((k : ℝ) + 1) := by
    have hKnR : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hKn
    norm_num at hKnR
    linarith
  have hlin :
      Real.sqrt 3 * ((k : ℝ) + 1) <
        2 * ((n : ℝ) - ((k : ℝ) + 1)) := by
    unfold realCutoff at hnR
    nlinarith
  have hsquareR :
      3 * ((k : ℝ) + 1) ^ 2 <
        4 * ((n : ℝ) - ((k : ℝ) + 1)) ^ 2 := by
    have hleft0 : 0 ≤ Real.sqrt 3 * ((k : ℝ) + 1) := by positivity
    nlinarith [mul_pos (sub_pos.mpr hlin) (add_pos_of_nonneg_of_pos hleft0
      (by nlinarith : 0 < 2 * ((n : ℝ) - ((k : ℝ) + 1))))]
  have hsubCast : ((n - (k + 1) : ℕ) : ℝ) = (n : ℝ) - ((k : ℝ) + 1) := by
    rw [Nat.cast_sub hKn]
    norm_num
  rw [← hsubCast] at hsquareR
  have hsquare : 3 * (k + 1) ^ 2 < 4 * (n - (k + 1)) ^ 2 := by
    exact_mod_cast hsquareR
  exact h_eq_middle hk hn hsquare (by omega)

/-- Lemma `lem:B-equals-f` exactly as a three-branch formula using the
manuscript's floor and ceiling cutoffs. -/
theorem h_eq_piecewise_real {k n : ℕ} (hk : 2 ≤ k) (hn : k + 2 ≤ n) :
    h k n =
      if n ≤ Nat.floor (realCutoff k) then
        t k n
      else if n < (5 * k + 2) / 2 then
        (2 * n + (k + 1)) ^ 2 / 24
      else
        (k + 1) * (n - k - 1) := by
  by_cases hfirst : n ≤ Nat.floor (realCutoff k)
  · simp only [hfirst, if_true]
    exact h_eq_t_of_le_floor_realCutoff hn hfirst
  · simp only [hfirst, if_false]
    by_cases hterminal : n < (5 * k + 2) / 2
    · simp only [hterminal, if_true]
      exact h_eq_middle_of_floor_realCutoff_lt hk hn (by omega) hterminal
    · simp only [hterminal, if_false]
      exact h_eq_terminal hk (by omega)

/-- One-step persistence in Lemma `lem:linear-bound`: once the split
construction is strictly better, it remains so at the next order. -/
theorem p_gt_t_succ_of_p_gt_t {k m : ℕ} (hm : k + 1 ≤ m)
    (hcross : t k m < p k m) :
    t k (m + 1) < p k (m + 1) := by
  obtain ⟨a, haA, haGt⟩ := (Finset.lt_sup_iff.mp hcross)
  have haBounds := mem_A_iff.mp haA
  have haLower := haBounds.1
  have haUpper := haBounds.2
  have ham : a ≤ m := haUpper.trans hm
  have hK2a : k + 1 ≤ 2 * a := by
    have hq : 2 * ((k + 1) / 2) ≤ k + 1 := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) 2
    omega
  have htStep : t k (m + 1) ≤ t k m + a := by
    unfold t
    calc
      ((k + 1) * (m + 1)) / 2
          = ((k + 1) * m + (k + 1)) / 2 := by ring_nf
      _ ≤ ((k + 1) * m + 2 * a) / 2 :=
        Nat.div_le_div_right (Nat.add_le_add_left hK2a _)
      _ = ((k + 1) * m) / 2 + a := by
        rw [Nat.add_mul_div_left ((k + 1) * m) a (by omega)]
  have hnextTerm :
      splitTerm k m a + a = splitTerm k (m + 1) a := by
    exact (splitTerm_succ ham).symm
  have hnext : splitTerm k m a + a ≤ p k (m + 1) := by
    rw [hnextTerm]
    exact p_ge_splitTerm haA
  omega

/-- Main persistence assertion of Lemma `lem:linear-bound`. -/
theorem p_gt_t_of_crossing {k n₀ m : ℕ} (hn₀ : k + 2 ≤ n₀)
    (hcross : t k n₀ < p k n₀) (hm : n₀ ≤ m) :
    t k m < p k m := by
  induction m, hm using Nat.le_induction with
  | base => exact hcross
  | succ m hnm ih =>
      exact p_gt_t_succ_of_p_gt_t (by omega) ih

/-- Coarse numerical conclusion in Lemma `lem:linear-bound` (ii), which is
the form used by the later arithmetic estimates. -/
theorem le_two_mul_add_two_of_p_le_t {k n : ℕ} (hk : 2 ≤ k)
    (hn : k + 2 ≤ n) (hpt : p k n ≤ t k n) :
    n ≤ 2 * k + 2 := by
  by_contra hnot
  have hnLarge : 2 * k + 3 ≤ n := by omega
  have hlower := p_ge_terminal k n
  have hfloor : 2 * t k n ≤ (k + 1) * n := by
    unfold t
    simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * n) 2
  have hstrict : t k n < (k + 1) * (n - (k + 1)) := by
    have hsub : n - (k + 1) + (k + 1) = n := by omega
    nlinarith
  omega

/-- A first crossing exists; this packages the manuscript's “smallest
integer” in a way that avoids a separate classical-choice assumption. -/
def IsFirstCrossing (k n₀ : ℕ) : Prop :=
  k + 2 ≤ n₀ ∧ t k n₀ < p k n₀ ∧
    ∀ n, k + 2 ≤ n → n < n₀ → p k n ≤ t k n

theorem exists_firstCrossing (k : ℕ) (hk : 2 ≤ k) :
    ∃ n₀, IsFirstCrossing k n₀ := by
  let Q : ℕ → Prop := fun n => k + 2 ≤ n ∧ t k n < p k n
  have hQ : ∃ n, Q n := by
    refine ⟨2 * k + 3, by omega, ?_⟩
    have hge := p_ge_terminal k (2 * k + 3)
    have htFloor : 2 * t k (2 * k + 3) ≤ (k + 1) * (2 * k + 3) := by
      unfold t
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self ((k + 1) * (2 * k + 3)) 2
    have hterm :
        (k + 1) * ((2 * k + 3) - (k + 1)) = (k + 1) * (k + 2) := by
      congr 1
      omega
    rw [hterm] at hge
    nlinarith
  refine ⟨Nat.find hQ, ?_⟩
  have hspec := Nat.find_spec hQ
  refine ⟨hspec.1, hspec.2, ?_⟩
  intro n hn hnmin
  have hnot : ¬ Q n := Nat.find_min hQ hnmin
  simp only [Q] at hnot
  omega

/-- Complete order-theoretic content of Lemma `lem:linear-bound`: the first
crossing persists, and every order at which `p_k ≤ t_k` is at most `2k+2`. -/
theorem linear_bound_discrete {k n₀ : ℕ} (hk : 2 ≤ k)
    (hfirst : IsFirstCrossing k n₀) :
    (∀ m ≥ n₀, t k m < p k m) ∧
      (∀ n ≥ k + 2, p k n ≤ t k n → n ≤ 2 * k + 2) := by
  constructor
  · intro m hm
    exact p_gt_t_of_crossing hfirst.1 hfirst.2.1 hm
  · intro n hn hle
    exact le_two_mul_add_two_of_p_le_t hk hn hle

private theorem sqrt_three_bounds : (3 / 2 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonneg := Real.sqrt_nonneg 3
  constructor <;> nlinarith

private theorem p_gt_t_at_ceil_realCutoff_add_one {k : ℕ} (hk : 4 ≤ k) :
    t k (Nat.ceil (realCutoff k) + 1) <
      p k (Nat.ceil (realCutoff k) + 1) := by
  let n := Nat.ceil (realCutoff k) + 1
  have hcutNonneg : 0 ≤ realCutoff k := by
    unfold realCutoff
    positivity
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg 3
  have hsLt := sqrt_three_bounds.2
  have hceilLower : realCutoff k ≤ (Nat.ceil (realCutoff k) : ℝ) :=
    Nat.le_ceil _
  have hnLowerR : realCutoff k + 1 ≤ (n : ℝ) := by
    dsimp [n]
    exact_mod_cast (show realCutoff k + 1 ≤ (Nat.ceil (realCutoff k) : ℝ) + 1 by
      linarith)
  have hceilUpper : Nat.ceil (realCutoff k) ≤ 2 * (k + 1) := by
    apply Nat.ceil_le.mpr
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hsLt)
      (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
    unfold realCutoff
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hn : k + 2 ≤ n := by
    have hbase : (k + 1 : ℝ) ≤ realCutoff k := by
      unfold realCutoff
      nlinarith
    have : k + 1 ≤ Nat.ceil (realCutoff k) := by
      exact_mod_cast hbase.trans hceilLower
    dsimp [n]
    omega
  have hnUpper : n ≤ (5 * k + 2) / 2 := by
    dsimp [n]
    have hlinNat : Nat.ceil (realCutoff k) + 1 ≤ 2 * (k + 1) + 1 := by omega
    omega
  have hKn : k + 1 ≤ n := by omega
  have hsubCast : ((n - (k + 1) : ℕ) : ℝ) = (n : ℝ) - (k + 1) := by
    rw [Nat.cast_sub hKn]
    norm_num
  have hlinR :
      Real.sqrt 3 * ((k : ℝ) + 1) + 2 ≤
        2 * ((n : ℝ) - ((k : ℝ) + 1)) := by
    unfold realCutoff at hnLowerR
    nlinarith
  have hDReal :
      3 * ((k : ℝ) + 1) ^ 2 + 24 ≤
        4 * ((n : ℝ) - ((k : ℝ) + 1)) ^ 2 := by
    have hK : (5 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (show 5 ≤ k + 1 by omega)
    have hsOne : (1 : ℝ) < Real.sqrt 3 := by nlinarith [sqrt_three_bounds.1]
    have hsK : (k : ℝ) + 1 ≤ Real.sqrt 3 * ((k : ℝ) + 1) := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hsOne)
        (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
    have hA0 : 0 ≤ Real.sqrt 3 * ((k : ℝ) + 1) + 2 := by positivity
    have hB0 : 0 ≤ 2 * ((n : ℝ) - ((k : ℝ) + 1)) := by
      have hKnR : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hKn
      norm_num at hKnR
      nlinarith
    have hsq := mul_nonneg (sub_nonneg.mpr hlinR) (add_nonneg hA0 hB0)
    nlinarith
  have hD :
      12 * ((k + 1) * n) + 24 ≤ (2 * n + (k + 1)) ^ 2 := by
    have hidR :
        (2 * (n : ℝ) + ((k : ℝ) + 1)) ^ 2 -
            12 * (((k : ℝ) + 1) * n) =
          4 * ((n : ℝ) - ((k : ℝ) + 1)) ^ 2 -
            3 * ((k : ℝ) + 1) ^ 2 := by ring
    have hDR :
        (12 : ℝ) * (((k + 1) * n : ℕ) : ℝ) + 24 ≤
          (((2 * n + (k + 1)) ^ 2 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
      nlinarith
    exact_mod_cast hDR
  have hDnat :
      3 * (k + 1) ^ 2 + 24 ≤ 4 * (n - (k + 1)) ^ 2 := by
    rw [← hsubCast] at hDReal
    exact_mod_cast hDReal
  have hfirst : 3 * (k + 1) ^ 2 < 4 * (n - (k + 1)) ^ 2 := by omega
  have hp := p_eq_middle (show 2 ≤ k by omega) hn hfirst hnUpper
  have htFloor : 24 * t k n ≤ 12 * ((k + 1) * n) := by
    have hfloor : 2 * t k n ≤ (k + 1) * n := by
      unfold t
      simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * n) 2
    nlinarith
  have htSucc : t k n + 1 ≤ (2 * n + (k + 1)) ^ 2 / 24 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 24)).mpr
    calc
      (t k n + 1) * 24 = 24 * t k n + 24 := by ring
      _ ≤ 12 * ((k + 1) * n) + 24 := by omega
      _ ≤ (2 * n + (k + 1)) ^ 2 := hD
  change t k n < p k n
  rw [hp]
  omega

/-- Lemma `lem:linear-bound` with the manuscript's exact floor/ceiling
cutoffs. -/
theorem linear_bound_real {k n₀ : ℕ} (hk : 2 ≤ k)
    (hfirst : IsFirstCrossing k n₀) :
    (Nat.floor (realCutoff k) + 1 ≤ n₀ ∧
      n₀ ≤ Nat.ceil (realCutoff k) + 1) ∧
    (∀ n, k + 2 ≤ n → p k n ≤ t k n →
      n ≤ Nat.ceil (realCutoff k) ∧
        Nat.ceil (realCutoff k) ≤ 2 * k + 2) := by
  have hcutNonneg : 0 ≤ realCutoff k := by
    unfold realCutoff
    positivity
  have hsLt := sqrt_three_bounds.2
  have hceilCoarse : Nat.ceil (realCutoff k) ≤ 2 * k + 2 := by
    apply Nat.ceil_le.mpr
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hsLt)
      (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
    unfold realCutoff
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hlower : Nat.floor (realCutoff k) + 1 ≤ n₀ := by
    by_contra hnot
    have hnFloor : n₀ ≤ Nat.floor (realCutoff k) := by omega
    have hn0Lower := hfirst.1
    have hsquare := square_le_of_le_floor_realCutoff
      (show k + 1 ≤ n₀ by omega) hnFloor
    have hh := h_eq_t_of_square_le hfirst.1 hsquare
    have hpH := p_le_h (k := k) (n := n₀) hfirst.1
    rw [hh] at hpH
    have hcross0 := hfirst.2.1
    omega
  have hupper : n₀ ≤ Nat.ceil (realCutoff k) + 1 := by
    by_cases hk4 : 4 ≤ k
    · have hcross := p_gt_t_at_ceil_realCutoff_add_one hk4
      by_contra hnot
      have hbefore := hfirst.2.2 (Nat.ceil (realCutoff k) + 1) (by
        have hbase : (k + 1 : ℝ) ≤ realCutoff k := by
          unfold realCutoff
          have hm := mul_nonneg (Real.sqrt_nonneg 3)
            (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
          nlinarith
        have hceilBase : k + 1 ≤ Nat.ceil (realCutoff k) := by
          exact_mod_cast hbase.trans (Nat.le_ceil (realCutoff k))
        omega) (by omega)
      omega
    · have hkSmall : k = 2 ∨ k = 3 := by omega
      have hsLower := sqrt_three_bounds.1
      have hceilLower : 2 * (k + 1) ≤ Nat.ceil (realCutoff k) := by
        have hlt : 2 * (k + 1) - 1 < Nat.ceil (realCutoff k) := by
          apply Nat.lt_ceil.mpr
          unfold realCutoff
          rcases hkSmall with rfl | rfl <;> norm_num at * <;> nlinarith
        omega
      have hn0Coarse : n₀ ≤ 2 * k + 3 := by
        by_contra hnot
        have hcross : t k (2 * k + 3) < p k (2 * k + 3) := by
          have hge := p_ge_terminal k (2 * k + 3)
          have htFloor : 2 * t k (2 * k + 3) ≤ (k + 1) * (2 * k + 3) := by
            unfold t
            simpa [Nat.mul_comm] using
              Nat.div_mul_le_self ((k + 1) * (2 * k + 3)) 2
          have htermEq :
              (k + 1) * (2 * k + 3 - (k + 1)) = (k + 1) * (k + 2) := by
            congr 1
            omega
          rw [htermEq] at hge
          nlinarith
        have hbefore := hfirst.2.2 (2 * k + 3) (by omega) (by omega)
        omega
      omega
  refine ⟨⟨hlower, hupper⟩, ?_⟩
  intro n hn hpt
  have hn0 : n < n₀ := by
    by_contra hnot
    have hcross := p_gt_t_of_crossing hfirst.1 hfirst.2.1
      (show n₀ ≤ n by omega)
    omega
  exact ⟨by omega, hceilCoarse⟩

private theorem two_mul_choose_two_le (r : ℕ) :
    2 * r.choose 2 ≤ r * (r - 1) := by
  rw [Nat.choose_two_right]
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (r * (r - 1)) 2

private theorem choose_add_choose_le_choose_add_sub_one {x y : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    x.choose 2 + y.choose 2 ≤ (x + y - 1).choose 2 := by
  have hxsub : x - 1 + 1 = x := by omega
  have hysub : y - 1 + 1 = y := by omega
  have hzsub : x + y - 1 - 1 + 1 = x + y - 1 := by omega
  have hx2 := two_mul_choose_two_le x
  have hy2 := two_mul_choose_two_le y
  rw [Nat.choose_two_right x, Nat.choose_two_right y,
    Nat.choose_two_right (x + y - 1)]
  have hxz : x ≤ x + y - 1 := by omega
  have hyz : y ≤ x + y - 1 := by omega
  have hxmul := Nat.mul_le_mul_right (x - 1) hxz
  have hymul := Nat.mul_le_mul_right (y - 1) hyz
  have hsubs : (x - 1) + (y - 1) = x + y - 1 - 1 := by omega
  calc
    x * (x - 1) / 2 + y * (y - 1) / 2
        ≤ (x * (x - 1) + y * (y - 1)) / 2 :=
          Nat.add_div_le_add_div _ _ _
    _ ≤ ((x + y - 1) * (x + y - 1 - 1)) / 2 := by
      apply Nat.div_le_div_right
      calc
        x * (x - 1) + y * (y - 1)
            ≤ (x + y - 1) * (x - 1) +
                (x + y - 1) * (y - 1) := by omega
        _ = (x + y - 1) * (x + y - 1 - 1) := by
          rw [← Nat.mul_add, hsubs]

private theorem choose_add_choose_le_t {k x y : ℕ}
    (hx0 : 1 ≤ x) (hy0 : 1 ≤ y)
    (hxK : x ≤ k + 1) (hyK : y ≤ k + 1)
    (hz : k + 2 ≤ x + y - 1) :
    x.choose 2 + y.choose 2 ≤ t k (x + y - 1) := by
  have hxsub : x - 1 + 1 = x := by omega
  have hysub : y - 1 + 1 = y := by omega
  have hxKsub : k + 1 - x + x = k + 1 := by omega
  have hyKsub : k + 1 - y + y = k + 1 := by omega
  have hx2 := two_mul_choose_two_le x
  have hy2 := two_mul_choose_two_le y
  have hpoly :
      x * (x - 1) + y * (y - 1) ≤ (k + 1) * (x + y - 1) := by
    have hxmul := Nat.mul_le_mul_right (x - 1) hxK
    have hymul := Nat.mul_le_mul_right (y - 1) hyK
    have hsubs : (x - 1) + (y - 1) ≤ x + y - 1 := by omega
    calc
      x * (x - 1) + y * (y - 1)
          ≤ (k + 1) * (x - 1) + (k + 1) * (y - 1) := by omega
      _ = (k + 1) * ((x - 1) + (y - 1)) := by rw [Nat.mul_add]
      _ ≤ (k + 1) * (x + y - 1) := Nat.mul_le_mul_left _ hsubs
  unfold t
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  nlinarith

private theorem choose_le_a_mul_sub_one {k x a : ℕ}
    (_hx : 1 ≤ x) (hxK : x ≤ k + 1) (ha : a ∈ A k) :
    x.choose 2 ≤ a * (x - 1) := by
  have haLower := (mem_A_iff.mp ha).1
  have hq : 2 * ((k + 1) / 2) ≤ k + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) 2
  have hxa : x ≤ 2 * a := by omega
  have hx2 := two_mul_choose_two_le x
  have hmul := Nat.mul_le_mul_right (x - 1) hxa
  nlinarith

private theorem splitTerm_add_right {k m a d : ℕ} (ha : a ≤ m) :
    splitTerm k (m + d) a = splitTerm k m a + a * d := by
  have hsub : m + d - a = (m - a) + d := by omega
  simp only [splitTerm, hsub, Nat.mul_add]
  omega

private theorem exists_splitTerm_eq_p (k n : ℕ) :
    ∃ a ∈ A k, p k n = splitTerm k n a := by
  have hA : (A k).Nonempty := ⟨k + 1, top_mem_A k⟩
  simpa [p] using Finset.exists_mem_eq_sup (A k) hA (splitTerm k n)

private theorem t_le_a_mul_sub_one {k m a : ℕ}
    (hm : k + 2 ≤ m) (ha : a ∈ A k) :
    t k m ≤ a * (m - 1) := by
  have haLower := (mem_A_iff.mp ha).1
  have hq : 2 * ((k + 1) / 2) ≤ k + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) 2
  have hK2a : k + 2 ≤ 2 * a := by omega
  have hmSub : m - 1 + 1 = m := by omega
  have hKm : k + 1 ≤ m - 1 := by omega
  have hd1 : 1 ≤ 2 * a - (k + 1) := by omega
  have hprod : k + 1 ≤ (2 * a - (k + 1)) * (m - 1) := by
    have hone := Nat.mul_le_mul_right (m - 1) hd1
    have hone' : m - 1 ≤ (2 * a - (k + 1)) * (m - 1) := by
      simpa using hone
    exact hKm.trans hone'
  have hmul : (k + 1) * m ≤ 2 * a * (m - 1) := by
    have hcancel : 2 * a - (k + 1) + (k + 1) = 2 * a := by omega
    nlinarith
  have hfloor : 2 * t k m ≤ (k + 1) * m := by
    unfold t
    simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * m) 2
  nlinarith

/-- Claim `claim:h_k(n)-merge` from the proof of Lemma `lem:merge-ineq`.
If the split-construction maximum is strictly below `h_k(m)`, then the
nearly-regular branch is active and is bounded by `a(m-1)` for every
admissible `a`. -/
theorem h_le_mul_sub_one_of_p_lt_h {k m a : ℕ}
    (hm : k + 2 ≤ m) (ha : a ∈ A k)
    (hgt : p k m < h k m) :
    h k m ≤ a * (m - 1) := by
  rw [h_eq_max hm] at hgt ⊢
  have hpt : p k m < t k m := by omega
  rw [max_eq_left (Nat.le_of_lt hpt)]
  exact t_le_a_mul_sub_one hm ha

private theorem splitTerm_le_a_mul_sub_one {k m a : ℕ}
    (hk : 3 ≤ k) (hm : k + 2 ≤ m) (ha : a ∈ A k) :
    splitTerm k m a ≤ a * (m - 1) := by
  have haBounds := mem_A_iff.mp ha
  have haLower := haBounds.1
  have haUpper := haBounds.2
  have hq : 2 * ((k + 1) / 2) ≤ k + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) 2
  have ha1 : 1 ≤ a := by omega
  have h3a : k + 3 ≤ 3 * a := by omega
  have hdiff : k + 1 - a ≤ 2 * (a - 1) := by omega
  have hfloor :
      2 * ((a * (k + 1 - a)) / 2) ≤ a * (k + 1 - a) := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (a * (k + 1 - a)) 2
  have hfloorBound : (a * (k + 1 - a)) / 2 ≤ a * (a - 1) := by
    have hmul := Nat.mul_le_mul_left a hdiff
    nlinarith
  have ham : a ≤ m := haUpper.trans (by omega)
  have hsubA : m - a + a = m := by omega
  have hsub1 : m - 1 + 1 = m := by omega
  unfold splitTerm
  calc
    a * (m - a) + a * (k + 1 - a) / 2
        ≤ a * (m - a) + a * (a - 1) :=
          Nat.add_le_add_left hfloorBound _
    _ = a * (m - 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega

private theorem h_eq_choose_of_le {k m : ℕ} (hm : m ≤ k + 1) :
    h k m = m.choose 2 := by
  simp [h, hm]

private theorem h_eq_p_of_le {k m : ℕ} (hm : k + 2 ≤ m)
    (hle : t k m ≤ p k m) : h k m = p k m := by
  rw [h_eq_max hm]
  exact max_eq_right hle

private theorem h_eq_t_of_le {k m : ℕ} (hm : k + 2 ≤ m)
    (hle : p k m ≤ t k m) : h k m = t k m := by
  rw [h_eq_max hm]
  exact max_eq_left hle

/-- Lemma `lem:merge-ineq` (i). -/
theorem merge_ineq_sub_one {k n x y : ℕ} (hk : 2 ≤ k)
    (hn0 : k + 2 ≤ n) (hn1 : n ≤ (5 * k + 2) / 2)
    (hcross : t k n < p k n)
    (hx0 : 1 ≤ x) (hy0 : 1 ≤ y) (hxy : x + y - 1 ≤ n) :
    h k x + h k y ≤ h k (x + y - 1) := by
  have hk3 : 3 ≤ k := by
    by_contra hknot
    have hk2 : k = 2 := by omega
    subst k
    interval_cases n <;> norm_num [t, p, A, splitTerm] at hcross <;>
      rcases hcross with ⟨b, hb, hgt⟩ <;>
      rcases hb with ⟨hb0, hb1⟩ <;>
      interval_cases b <;> norm_num [splitTerm] at *
  by_cases hxK : x ≤ k + 1
  · rw [h_eq_choose_of_le hxK]
    by_cases hyK : y ≤ k + 1
    · rw [h_eq_choose_of_le hyK]
      by_cases hzK : x + y - 1 ≤ k + 1
      · rw [h_eq_choose_of_le hzK]
        exact choose_add_choose_le_choose_add_sub_one hx0 hy0
      · have hz : k + 2 ≤ x + y - 1 := by omega
        exact (choose_add_choose_le_t hx0 hy0 hxK hyK hz).trans
          (t_le_h hz)
    · have hyLarge : k + 2 ≤ y := by omega
      have hzLarge : k + 2 ≤ x + y - 1 := by omega
      by_cases hpy : t k y ≤ p k y
      · rw [h_eq_p_of_le hyLarge hpy]
        obtain ⟨a, haA, hpa⟩ := exists_splitTerm_eq_p k y
        rw [hpa]
        have hchoose := choose_le_a_mul_sub_one hx0 hxK haA
        have haY : a ≤ y := (mem_A_iff.mp haA).2.trans (by omega)
        have hadd := splitTerm_add_right (k := k) (m := y) (a := a)
          (d := x - 1) haY
        have hsum : y + (x - 1) = x + y - 1 := by omega
        rw [hsum] at hadd
        have hpz := p_ge_splitTerm (n := x + y - 1) haA
        have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
        rw [hadd] at hpz
        omega
      · have hpy' : p k y ≤ t k y := by omega
        rw [h_eq_t_of_le hyLarge hpy']
        have hx2 := two_mul_choose_two_le x
        have hinc : x * (x - 1) ≤ (k + 1) * (x - 1) :=
          Nat.mul_le_mul_right (x - 1) hxK
        have hty : 2 * t k y ≤ (k + 1) * y := by
          unfold t
          simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * y) 2
        have htarget : x.choose 2 + t k y ≤ t k (x + y - 1) := by
          unfold t
          apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
          calc
            (x.choose 2 + ((k + 1) * y) / 2) * 2
                = 2 * x.choose 2 + 2 * (((k + 1) * y) / 2) := by omega
            _ ≤ (k + 1) * (x - 1) + (k + 1) * y := by omega
            _ = (k + 1) * (x + y - 1) := by
              rw [← Nat.mul_add]
              congr 1
              omega
        exact htarget.trans (t_le_h hzLarge)
  · have hxLarge : k + 2 ≤ x := by omega
    by_cases hyK : y ≤ k + 1
    · rw [h_eq_choose_of_le hyK]
      have hzLarge : k + 2 ≤ x + y - 1 := by omega
      by_cases hpx : t k x ≤ p k x
      · rw [h_eq_p_of_le hxLarge hpx]
        obtain ⟨a, haA, hpa⟩ := exists_splitTerm_eq_p k x
        rw [hpa]
        have hchoose := choose_le_a_mul_sub_one hy0 hyK haA
        have haX : a ≤ x := (mem_A_iff.mp haA).2.trans (by omega)
        have hadd := splitTerm_add_right (k := k) (m := x) (a := a)
          (d := y - 1) haX
        have hsum : x + (y - 1) = x + y - 1 := by omega
        rw [hsum] at hadd
        have hpz := p_ge_splitTerm (n := x + y - 1) haA
        have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
        rw [hadd] at hpz
        omega
      · have hpx' : p k x ≤ t k x := by omega
        rw [h_eq_t_of_le hxLarge hpx']
        have hy2 := two_mul_choose_two_le y
        have hinc : y * (y - 1) ≤ (k + 1) * (y - 1) :=
          Nat.mul_le_mul_right (y - 1) hyK
        have htx : 2 * t k x ≤ (k + 1) * x := by
          unfold t
          simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * x) 2
        have htarget : t k x + y.choose 2 ≤ t k (x + y - 1) := by
          unfold t
          apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
          calc
            (((k + 1) * x) / 2 + y.choose 2) * 2
                = 2 * (((k + 1) * x) / 2) + 2 * y.choose 2 := by omega
            _ ≤ (k + 1) * x + (k + 1) * (y - 1) := by omega
            _ = (k + 1) * (x + y - 1) := by
              rw [← Nat.mul_add]
              congr 1
              omega
        exact htarget.trans (t_le_h hzLarge)
    · have hyLarge : k + 2 ≤ y := by omega
      have hzLarge : k + 2 ≤ x + y - 1 := by omega
      by_cases hpx : t k x ≤ p k x
      · rw [h_eq_p_of_le hxLarge hpx]
        obtain ⟨a, haA, hpa⟩ := exists_splitTerm_eq_p k x
        rw [hpa]
        by_cases hpy : t k y ≤ p k y
        · rw [h_eq_p_of_le hyLarge hpy]
          obtain ⟨b, hbA, hpb⟩ := exists_splitTerm_eq_p k y
          rw [hpb]
          by_cases hab : a ≤ b
          · have hax := splitTerm_le_a_mul_sub_one hk3 hxLarge haA
            have habMul : a * (x - 1) ≤ b * (x - 1) :=
              Nat.mul_le_mul_right (x - 1) hab
            have hbY : b ≤ y := (mem_A_iff.mp hbA).2.trans (by omega)
            have hadd := splitTerm_add_right (k := k) (m := y) (a := b)
              (d := x - 1) hbY
            have hsum : y + (x - 1) = x + y - 1 := by omega
            rw [hsum] at hadd
            have hpz := p_ge_splitTerm (n := x + y - 1) hbA
            have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
            rw [hadd] at hpz
            omega
          · have hba : b ≤ a := by omega
            have hby := splitTerm_le_a_mul_sub_one hk3 hyLarge hbA
            have hbaMul : b * (y - 1) ≤ a * (y - 1) :=
              Nat.mul_le_mul_right (y - 1) hba
            have haX : a ≤ x := (mem_A_iff.mp haA).2.trans (by omega)
            have hadd := splitTerm_add_right (k := k) (m := x) (a := a)
              (d := y - 1) haX
            have hsum : x + (y - 1) = x + y - 1 := by omega
            rw [hsum] at hadd
            have hpz := p_ge_splitTerm (n := x + y - 1) haA
            have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
            rw [hadd] at hpz
            omega
        · have hpy' : p k y ≤ t k y := by omega
          rw [h_eq_t_of_le hyLarge hpy']
          have hty := t_le_a_mul_sub_one hyLarge haA
          have haX : a ≤ x := (mem_A_iff.mp haA).2.trans (by omega)
          have hadd := splitTerm_add_right (k := k) (m := x) (a := a)
            (d := y - 1) haX
          have hsum : x + (y - 1) = x + y - 1 := by omega
          rw [hsum] at hadd
          have hpz := p_ge_splitTerm (n := x + y - 1) haA
          have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
          rw [hadd] at hpz
          omega
      · have hpx' : p k x ≤ t k x := by omega
        rw [h_eq_t_of_le hxLarge hpx']
        by_cases hpy : t k y ≤ p k y
        · rw [h_eq_p_of_le hyLarge hpy]
          obtain ⟨b, hbA, hpb⟩ := exists_splitTerm_eq_p k y
          rw [hpb]
          have htx := t_le_a_mul_sub_one hxLarge hbA
          have hbY : b ≤ y := (mem_A_iff.mp hbA).2.trans (by omega)
          have hadd := splitTerm_add_right (k := k) (m := y) (a := b)
            (d := x - 1) hbY
          have hsum : y + (x - 1) = x + y - 1 := by omega
          rw [hsum] at hadd
          have hpz := p_ge_splitTerm (n := x + y - 1) hbA
          have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
          rw [hadd] at hpz
          omega
        · have hpy' : p k y ≤ t k y := by omega
          rw [h_eq_t_of_le hyLarge hpy']
          have htx : 2 * t k x ≤ (k + 1) * x := by
            unfold t
            simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * x) 2
          have hty : 2 * t k y ≤ (k + 1) * y := by
            unfold t
            simpa [Nat.mul_comm] using Nat.div_mul_le_self ((k + 1) * y) 2
          have hpz := p_ge_terminal k (x + y - 1)
          have hpzh := p_le_h (k := k) (n := x + y - 1) hzLarge
          have hsub : x + y - 1 - (k + 1) + (k + 1) = x + y - 1 := by
            omega
          have hsumLower : 2 * (k + 1) ≤ x + y := by omega
          have hlin : x + y ≤ 2 * (x + y - 1 - (k + 1)) := by omega
          have hmul := Nat.mul_le_mul_left (k + 1) hlin
          have hdouble :
              2 * (t k x + t k y) ≤
                2 * ((k + 1) * (x + y - 1 - (k + 1))) := by
            calc
              2 * (t k x + t k y) = 2 * t k x + 2 * t k y := by omega
              _ ≤ (k + 1) * x + (k + 1) * y := by omega
              _ = (k + 1) * (x + y) := by ring
              _ ≤ (k + 1) * (2 * (x + y - 1 - (k + 1))) := hmul
              _ = 2 * ((k + 1) * (x + y - 1 - (k + 1))) := by ring
          omega

/-- Monotonicity used in Lemma `lem:merge-ineq` (ii). -/
theorem h_mono_succ {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    h k m ≤ h k (m + 1) := by
  by_cases hmSmall : m ≤ k
  · have hmK : m ≤ k + 1 := by omega
    have hmsK : m + 1 ≤ k + 1 := by omega
    rw [h_eq_choose_of_le hmK, h_eq_choose_of_le hmsK,
      Nat.choose_two_right, Nat.choose_two_right]
    apply Nat.div_le_div_right
    have hsub1 : m - 1 ≤ m + 1 - 1 := by omega
    exact Nat.mul_le_mul (by omega) hsub1
  · by_cases hmBoundary : m = k + 1
    · subst m
      rw [h_eq_choose_of_le (by omega : k + 1 ≤ k + 1),
        Nat.choose_two_right]
      have ht := t_le_h (k := k) (n := k + 2) (by omega)
      apply le_trans ?_ ht
      unfold t
      apply Nat.div_le_div_right
      have hsub1 : k + 1 - 1 ≤ k + 2 := by omega
      exact Nat.mul_le_mul_left (k + 1) hsub1
    · have hmLarge : k + 2 ≤ m := by omega
      have hmsLarge : k + 2 ≤ m + 1 := by omega
      have ht : t k m ≤ t k (m + 1) := by
        unfold t
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul_left (k + 1) (by omega)
      have hp : p k m ≤ p k (m + 1) := by
        obtain ⟨a, haA, hpa⟩ := exists_splitTerm_eq_p k m
        have ham : a ≤ m := (mem_A_iff.mp haA).2.trans (by omega)
        have hnext := p_ge_splitTerm (n := m + 1) haA
        rw [splitTerm_succ ham, ← hpa] at hnext
        omega
      rw [h_eq_max hmLarge, h_eq_max hmsLarge]
      exact max_le_max ht hp

/-- Lemma `lem:merge-ineq` (ii). -/
theorem merge_ineq {k n x y : ℕ} (hk : 2 ≤ k)
    (hn0 : k + 2 ≤ n) (hn1 : n ≤ (5 * k + 2) / 2)
    (hcross : t k n < p k n)
    (hx0 : 1 ≤ x) (hy0 : 1 ≤ y) (hxy : x + y ≤ n) :
    h k x + h k y ≤ h k (x + y) := by
  have hmerge := merge_ineq_sub_one hk hn0 hn1 hcross hx0 hy0 (by omega)
  have hmono := h_mono_succ hk (show 1 ≤ x + y - 1 by omega)
  have hsucc : x + y - 1 + 1 = x + y := by omega
  rw [hsucc] at hmono
  exact hmerge.trans hmono

/-- Lemma `lem:merge-ineq`, with its two conclusions bundled together. -/
theorem merge_ineq_both {k n : ℕ} (hk : 2 ≤ k)
    (hn0 : k + 2 ≤ n) (hn1 : n ≤ (5 * k + 2) / 2)
    (hcross : t k n < p k n) :
    (∀ x y, 1 ≤ x → 1 ≤ y → x + y - 1 ≤ n →
      h k x + h k y ≤ h k (x + y - 1)) ∧
    (∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ n →
      h k x + h k y ≤ h k (x + y)) := by
  constructor
  · intro x y hx hy hxy
    exact merge_ineq_sub_one hk hn0 hn1 hcross hx hy hxy
  · intro x y hx hy hxy
    exact merge_ineq hk hn0 hn1 hcross hx hy hxy

/-- The common auxiliary quantity used in the proof of
`lem:cycle-arithmetic-consequences`. -/
def cycleQ (k n c u ε : ℕ) : ℕ :=
  (u - 1) * (n - c) +
    (((u - 1 - ε) * (u - ε) + (c - u + 1 + ε) * (k + 1)) / 2)

private theorem cycleQ_le_t_of_small_coefficient {k n c u ε : ℕ}
    (hc : c < n) (hu0 : 1 + ε ≤ u) (huC : u ≤ c / 2)
    (huK : u ≤ k + 1 + ε) (hcoef : 2 * u ≤ k + 3) :
    cycleQ k n c u ε ≤ t k n := by
  have h2u : 2 * u ≤ c := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp huC
  have hcn : c ≤ n := by omega
  have hnc : n - c + c = n := by omega
  have hu1 : u - 1 + 1 = u := by omega
  have hue1 : u - 1 - ε + (1 + ε) = u := by omega
  have hue : u - ε + ε = u := by omega
  have hcu : c - u + u = c := by omega
  have hfloor :
      2 * ((((u - 1 - ε) * (u - ε) +
          (c - u + 1 + ε) * (k + 1))) / 2) ≤
        (u - 1 - ε) * (u - ε) +
          (c - u + 1 + ε) * (k + 1) := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self
      ((u - 1 - ε) * (u - ε) + (c - u + 1 + ε) * (k + 1)) 2
  unfold cycleQ t
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  nlinarith

set_option maxHeartbeats 1000000 in
-- The two nonlinear integer branches require an expanded normalization budget.
private theorem cycleQ_le_t_of_p_le {k n c u ε : ℕ}
    (hk : 3 ≤ k) (hn : k + 2 ≤ n) (hc : c < n)
    (hε : ε ≤ 1) (hu0 : 1 + ε ≤ u) (huC : u ≤ c / 2)
    (hpt : p k n ≤ t k n) :
    cycleQ k n c u ε ≤ t k n := by
  have hnUpper := le_two_mul_add_two_of_p_le_t (by omega) hn hpt
  have h2u : 2 * u ≤ c := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp huC
  have huK : u ≤ k := by omega
  by_cases hcoef : 2 * u ≤ k + 3
  · exact cycleQ_le_t_of_small_coefficient hc hu0 huC (by omega) hcoef
  · have hq : 2 * ((k + 1) / 2) ≤ k + 1 := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) 2
    have huLower : (k + 1) / 2 + 1 ≤ u := by omega
    have huA : u ∈ A k := mem_A_iff.mpr ⟨huLower, by omega⟩
    have hsplit : splitTerm k n u ≤ t k n :=
      (p_ge_splitTerm huA).trans hpt
    have huN : u ≤ n := by omega
    have hKnU : u ≤ k + 1 := by omega
    have hnu : n - u + u = n := by omega
    have hKu : k + 1 - u + u = k + 1 := by omega
    have hcn : n - c + c = n := by omega
    have hcu : c - u + u = c := by omega
    have hFloorLower :
        u * (k + 1 - u) ≤ 2 * ((u * (k + 1 - u)) / 2) + 1 := by
      have hlt :
          u * (k + 1 - u) <
            (((u * (k + 1 - u)) / 2) + 1) * 2 := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp
        omega
      omega
    have hSplitDouble :
        2 * (u * (n - u) + (u * (k + 1 - u)) / 2) ≤
          (k + 1) * n := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hsplit
      simpa [splitTerm, t, Nat.mul_comm] using this
    have hMuFloor :
        2 * ((((u - 1 - ε) * (u - ε) +
          (c - u + 1 + ε) * (k + 1))) / 2) ≤
          (u - 1 - ε) * (u - ε) +
            (c - u + 1 + ε) * (k + 1) := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self
        ((u - 1 - ε) * (u - ε) + (c - u + 1 + ε) * (k + 1)) 2
    have hMainZ :
        (2 * (u : ℤ) - ((k : ℤ) + 1)) * (n : ℤ) ≤
          3 * (u : ℤ) ^ 2 - ((k : ℤ) + 1) * u + 1 := by
      have hSplitZ :
          (2 : ℤ) * ((u : ℤ) * ((n : ℤ) - u) +
            ((u * (k + 1 - u) / 2 : ℕ) : ℤ)) ≤
            ((k : ℤ) + 1) * n := by
        exact_mod_cast hSplitDouble
      have hFloorZ :
          (u : ℤ) * (((k : ℤ) + 1) - u) ≤
            2 * ((u * (k + 1 - u) / 2 : ℕ) : ℤ) + 1 := by
        simpa [Nat.cast_sub hKnU] using (by exact_mod_cast hFloorLower)
      nlinarith
    have hApos : (3 : ℤ) ≤ 2 * (u : ℤ) - ((k : ℤ) + 1) := by
      omega
    rcases (show ε = 0 ∨ ε = 1 by omega) with hε0 | hε1
    · subst ε
      have hmult := mul_le_mul_of_nonneg_left hMainZ (by omega :
        (0 : ℤ) ≤ 2 * (u : ℤ) - ((k : ℤ) + 1) - 2)
      have hnum :
          (0 : ℤ) ≤ ((k : ℤ) + 3) * ((k : ℤ) - u) + 4 := by
        have hku : (0 : ℤ) ≤ (k : ℤ) - u := by omega
        positivity
      have hpsi :
          (2 * (u : ℤ) - ((k : ℤ) + 1) - 2) *
              ((n : ℤ) - 2 * u) ≤
            ((u : ℤ) - 1) * (((k : ℤ) + 1) - u) := by
        nlinarith
      have hpsiC :
          (2 * (u : ℤ) - ((k : ℤ) + 1) - 2) *
              ((n : ℤ) - c) ≤
            ((u : ℤ) - 1) * (((k : ℤ) + 1) - u) := by
        nlinarith
      have hRestZ :
          (2 : ℤ) * ((u : ℤ) - 1) * ((n : ℤ) - c) +
              ((u : ℤ) - 1) * u +
              ((c : ℤ) - u + 1) * ((k : ℤ) + 1) ≤
            ((k : ℤ) + 1) * n := by
        have hid :
            (2 : ℤ) * ((u : ℤ) - 1) * ((n : ℤ) - c) +
                ((u : ℤ) - 1) * u +
                ((c : ℤ) - u + 1) * ((k : ℤ) + 1) -
                ((k : ℤ) + 1) * n =
              (2 * (u : ℤ) - ((k : ℤ) + 1) - 2) * ((n : ℤ) - c) -
                ((u : ℤ) - 1) * (((k : ℤ) + 1) - u) := by ring
        linarith
      have hRest :
          2 * (u - 1) * (n - c) + (u - 1) * u +
              (c - u + 1) * (k + 1) ≤ (k + 1) * n := by
        have hu1Z : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
        have hncZ : ((n - c : ℕ) : ℤ) = (n : ℤ) - c := by omega
        have hcuZ : ((c - u : ℕ) : ℤ) = (c : ℤ) - u := by omega
        rw [← hu1Z, ← hncZ, ← hcuZ] at hRestZ
        exact_mod_cast hRestZ
      unfold cycleQ t
      simp only [Nat.sub_zero, Nat.add_zero]
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
      calc
        ((u - 1) * (n - c) +
            ((u - 1) * u + (c - u + 1) * (k + 1)) / 2) * 2
            = 2 * (u - 1) * (n - c) +
                2 * (((u - 1) * u + (c - u + 1) * (k + 1)) / 2) := by
              ring
        _ ≤ 2 * (u - 1) * (n - c) +
              ((u - 1) * u + (c - u + 1) * (k + 1)) := by omega
        _ ≤ (k + 1) * n := by simpa [Nat.add_assoc] using hRest
    · subst ε
      have hmult := mul_le_mul_of_nonneg_left hMainZ (by omega :
        (0 : ℤ) ≤ 2 * (u : ℤ) - ((k : ℤ) + 1) - 2)
      have hnum :
          (0 : ℤ) ≤
            4 * (u : ℤ) ^ 2 - (5 * (k : ℤ) + 11) * u +
              2 * (k : ℤ) ^ 2 + 7 * k + 7 := by
        nlinarith [sq_nonneg (8 * (u : ℤ) - 5 * (k : ℤ) - 11),
          mul_nonneg (show (0 : ℤ) ≤ k - 1 by omega)
            (show (0 : ℤ) ≤ 7 * k + 9 by positivity)]
      have hpsi :
          (2 * (u : ℤ) - ((k : ℤ) + 1) - 2) *
              ((n : ℤ) - 2 * u) ≤
            ((u : ℤ) - 2) * (((k : ℤ) + 2) - u) := by
        nlinarith
      have hpsiC :
          (2 * (u : ℤ) - ((k : ℤ) + 1) - 2) *
              ((n : ℤ) - c) ≤
            ((u : ℤ) - 2) * (((k : ℤ) + 2) - u) := by
        have hncLe : (n : ℤ) - c ≤ (n : ℤ) - 2 * u := by omega
        have hcoefZ :
            (0 : ℤ) ≤ 2 * (u : ℤ) - ((k : ℤ) + 1) - 2 := by omega
        exact (mul_le_mul_of_nonneg_left hncLe hcoefZ).trans hpsi
      have hRestZ :
          (2 : ℤ) * ((u : ℤ) - 1) * ((n : ℤ) - c) +
              ((u : ℤ) - 2) * (u - 1) +
              ((c : ℤ) - u + 2) * ((k : ℤ) + 1) ≤
            ((k : ℤ) + 1) * n := by
        have hid :
            (2 : ℤ) * ((u : ℤ) - 1) * ((n : ℤ) - c) +
                ((u : ℤ) - 2) * (u - 1) +
                ((c : ℤ) - u + 2) * ((k : ℤ) + 1) -
                ((k : ℤ) + 1) * n =
              (2 * (u : ℤ) - ((k : ℤ) + 1) - 2) * ((n : ℤ) - c) -
                ((u : ℤ) - 2) * (((k : ℤ) + 2) - u) := by ring
        linarith
      have hRest :
          2 * (u - 1) * (n - c) + (u - 2) * (u - 1) +
              (c - u + 2) * (k + 1) ≤ (k + 1) * n := by
        have hu1Z : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
        have hu2Z : ((u - 2 : ℕ) : ℤ) = (u : ℤ) - 2 := by omega
        have hncZ : ((n - c : ℕ) : ℤ) = (n : ℤ) - c := by omega
        have hcuZ : ((c - u : ℕ) : ℤ) = (c : ℤ) - u := by omega
        rw [← hu1Z, ← hu2Z, ← hncZ, ← hcuZ] at hRestZ
        exact_mod_cast hRestZ
      unfold cycleQ t
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
      calc
        ((u - 1) * (n - c) +
            ((u - 2) * (u - 1) + (c - u + 2) * (k + 1)) / 2) * 2
            = 2 * (u - 1) * (n - c) +
                2 * (((u - 2) * (u - 1) + (c - u + 2) * (k + 1)) / 2) := by
              ring
        _ ≤ 2 * (u - 1) * (n - c) +
              ((u - 2) * (u - 1) + (c - u + 2) * (k + 1)) := by omega
        _ ≤ (k + 1) * n := by simpa [Nat.add_assoc] using hRest

set_option maxHeartbeats 1000000 in
-- Completing two parameterized quadratics needs a larger normalization budget.
private theorem cycleQ_le_h_of_p_gt {k n c u ε : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n) (hnUpper : n ≤ (5 * k + 2) / 2)
    (hc : c < n) (hε : ε ≤ 1) (hu0 : 1 + ε ≤ u) (huC : u ≤ c / 2)
    (hpt : t k n < p k n) :
    cycleQ k n c u ε ≤ h k n := by
  have h2u : 2 * u ≤ c := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp huC
  have hk4 : 4 ≤ k := by
    by_contra hnot
    have hkCases : k = 2 ∨ k = 3 := by omega
    rcases hkCases with rfl | rfl
    · interval_cases n <;> norm_num [t, p, A, splitTerm] at hpt <;>
        rcases hpt with ⟨b, hb, hgt⟩ <;> rcases hb with ⟨hb0, hb1⟩ <;>
        interval_cases b <;> norm_num [splitTerm] at *
    · interval_cases n <;> norm_num [t, p, A, splitTerm] at hpt <;>
        rcases hpt with ⟨b, hb, hgt⟩ <;> rcases hb with ⟨hb0, hb1⟩ <;>
        interval_cases b <;> norm_num [splitTerm] at *
  have hfirst : 3 * (k + 1) ^ 2 < 4 * (n - (k + 1)) ^ 2 := by
    by_contra hnot
    have hcut : 4 * (n - (k + 1)) ^ 2 ≤ 3 * (k + 1) ^ 2 := by omega
    have hh := h_eq_t_of_square_le hn hcut
    have hpH := p_le_h (k := k) (n := n) hn
    rw [hh] at hpH
    omega
  have hh := h_eq_middle hk hn hfirst hnUpper
  by_cases hcoef : 2 * u ≤ k + 3
  · have hqt := cycleQ_le_t_of_small_coefficient hc hu0 huC (by omega) hcoef
    exact hqt.trans (t_le_h hn)
  · have hu1 : 1 ≤ u := by omega
    have hu2 : 2 ≤ u := by omega
    have hcn : c ≤ n := by omega
    have hnc : n - c + c = n := by omega
    have hcu : c - u + u = c := by omega
    have hnu : 2 * u ≤ n := h2u.trans hcn
    have hnuSub : n - 2 * u + 2 * u = n := by omega
    have hcu2 : c - 2 * u + 2 * u = c := by omega
    have hMuFloor :
        2 * ((((u - 1 - ε) * (u - ε) +
          (c - u + 1 + ε) * (k + 1))) / 2) ≤
          (u - 1 - ε) * (u - ε) +
            (c - u + 1 + ε) * (k + 1) := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self
        ((u - 1 - ε) * (u - ε) + (c - u + 1 + ε) * (k + 1)) 2
    have hTwoQ :
        2 * cycleQ k n c u ε ≤
          2 * (u - 1) * (n - 2 * u) +
            (u - 1 - ε) * (u - ε) +
            (u + 1 + ε) * (k + 1) := by
      have hrest :
          2 * (u - 1) * (n - c) +
              (u - 1 - ε) * (u - ε) +
              (c - u + 1 + ε) * (k + 1) ≤
            2 * (u - 1) * (n - 2 * u) +
              (u - 1 - ε) * (u - ε) +
              (u + 1 + ε) * (k + 1) := by
        have heq :
            2 * (u - 1) * (n - 2 * u) +
                (u - 1 - ε) * (u - ε) +
                (u + 1 + ε) * (k + 1) =
              2 * (u - 1) * (n - c) +
                (u - 1 - ε) * (u - ε) +
                (c - u + 1 + ε) * (k + 1) +
                (c - 2 * u) * (2 * u - (k + 3)) := by
          have hnrel : n - 2 * u = (n - c) + (c - 2 * u) := by omega
          have hcurel : c - u = (c - 2 * u) + u := by omega
          have hcoefRel :
              k + 1 + (2 * u - (k + 3)) = 2 * (u - 1) := by omega
          have hmulRel := congrArg
            (fun z : ℕ => (c - 2 * u) * z) hcoefRel
          rw [hnrel, hcurel]
          nlinarith
        rw [heq]
        omega
      unfold cycleQ
      calc
        2 * ((u - 1) * (n - c) +
            (((u - 1 - ε) * (u - ε) +
              (c - u + 1 + ε) * (k + 1)) / 2))
            = 2 * (u - 1) * (n - c) +
                2 * (((u - 1 - ε) * (u - ε) +
                  (c - u + 1 + ε) * (k + 1)) / 2) := by ring
        _ ≤ 2 * (u - 1) * (n - c) +
              (u - 1 - ε) * (u - ε) +
              (c - u + 1 + ε) * (k + 1) := by omega
        _ ≤ _ := hrest
    have hdStrong : k + 3 ≤ 2 * (n - (k + 1)) := by
      by_contra hnot
      have hdle : 2 * (n - (k + 1)) ≤ k + 2 := by omega
      nlinarith
    have hlin0 : 18 * (k + 1) + 9 ≤ 12 * n := by omega
    have hlin1 : 26 * (k + 1) + 25 ≤ 20 * n := by omega
    rcases (show ε = 0 ∨ ε = 1 by omega) with hε0 | hε1
    · subst ε
      have hRZ :
          (12 : ℤ) *
              (2 * ((u : ℤ) - 1) * ((n : ℤ) - 2 * u) +
                ((u : ℤ) - 1) * u +
                ((u : ℤ) + 1) * ((k : ℤ) + 1)) ≤
            (2 * (n : ℤ) + ((k : ℤ) + 1)) ^ 2 := by
        nlinarith [sq_nonneg
          (2 * (n : ℤ) + ((k : ℤ) + 1) + 3 - 6 * (u : ℤ))]
      have hR :
          12 * (2 * (u - 1) * (n - 2 * u) +
              (u - 1) * u + (u + 1) * (k + 1)) ≤
            (2 * n + (k + 1)) ^ 2 := by
        have hu1Z : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
        have hnuZ : ((n - 2 * u : ℕ) : ℤ) = (n : ℤ) - 2 * u := by omega
        rw [← hu1Z, ← hnuZ] at hRZ
        exact_mod_cast hRZ
      rw [hh]
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 24)).mpr
      calc
        ((cycleQ k n c u 0) * 24)
            = 12 * (2 * cycleQ k n c u 0) := by ring
        _ ≤ 12 * (2 * (u - 1) * (n - 2 * u) +
              (u - 1) * u + (u + 1) * (k + 1)) :=
          Nat.mul_le_mul_left 12 hTwoQ
        _ ≤ (2 * n + (k + 1)) ^ 2 := hR
    · subst ε
      have hRZ :
          (12 : ℤ) *
              (2 * ((u : ℤ) - 1) * ((n : ℤ) - 2 * u) +
                ((u : ℤ) - 2) * (u - 1) +
                ((u : ℤ) + 2) * ((k : ℤ) + 1)) ≤
            (2 * (n : ℤ) + ((k : ℤ) + 1)) ^ 2 := by
        nlinarith [sq_nonneg
          (2 * (n : ℤ) + ((k : ℤ) + 1) + 1 - 6 * (u : ℤ))]
      have hR :
          12 * (2 * (u - 1) * (n - 2 * u) +
              (u - 2) * (u - 1) + (u + 2) * (k + 1)) ≤
            (2 * n + (k + 1)) ^ 2 := by
        have hu1Z : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
        have hu2Z : ((u - 2 : ℕ) : ℤ) = (u : ℤ) - 2 := by omega
        have hnuZ : ((n - 2 * u : ℕ) : ℤ) = (n : ℤ) - 2 * u := by omega
        rw [← hu1Z, ← hu2Z, ← hnuZ] at hRZ
        exact_mod_cast hRZ
      rw [hh]
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 24)).mpr
      have hTwoQ1 :
          2 * cycleQ k n c u 1 ≤
            2 * (u - 1) * (n - 2 * u) +
              (u - 2) * (u - 1) + (u + 2) * (k + 1) := by
        have hsubeq : u - 1 - 1 = u - 2 := by omega
        simpa [hsubeq, Nat.add_assoc] using hTwoQ
      calc
        ((cycleQ k n c u 1) * 24)
            = 12 * (2 * cycleQ k n c u 1) := by ring
        _ ≤ 12 * (2 * (u - 1) * (n - 2 * u) +
              (u - 2) * (u - 1) + (u + 2) * (k + 1)) :=
          Nat.mul_le_mul_left 12 hTwoQ1
        _ ≤ (2 * n + (k + 1)) ^ 2 := hR

/-- Common estimate from which both parts of
`lem:cycle-arithmetic-consequences` follow. -/
theorem cycleQ_le_h {k n c u ε : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n) (hnUpper : n ≤ (5 * k + 2) / 2)
    (hc : c < n) (hε : ε ≤ 1) (hu0 : 1 + ε ≤ u) (huC : u ≤ c / 2) :
    cycleQ k n c u ε ≤ h k n := by
  by_cases hk2 : k = 2
  · subst k
    have h2u : 2 * u ≤ c := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp huC
    have hcoef : 2 * u ≤ 2 + 3 := by omega
    have hqt := cycleQ_le_t_of_small_coefficient hc hu0 huC (by omega) hcoef
    exact hqt.trans (t_le_h hn)
  · have hk3 : 3 ≤ k := by omega
    by_cases hpt : p k n ≤ t k n
    · have hqt := cycleQ_le_t_of_p_le hk3 hn hc hε hu0 huC hpt
      exact hqt.trans (t_le_h hn)
    · exact cycleQ_le_h_of_p_gt hk hn hnUpper hc hε hu0 huC (by omega)

/-- `lem:cycle-arithmetic-consequences` (i). -/
theorem cycle_arithmetic_consequence_i {k n c s : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n) (hnUpper : n ≤ (5 * k + 2) / 2)
    (hc : c < n) (hs0 : 2 ≤ s) (hs1 : s ≤ c / 2 - 1) :
    s * (n - c) +
        (((s - 1) * s + (c - s + 1) * (k + 1)) / 2) ≤
      h k n := by
  have huC : s + 1 ≤ c / 2 := by omega
  have hQ := cycleQ_le_h hk hn hnUpper hc (show (1 : ℕ) ≤ 1 by omega)
    (show 1 + 1 ≤ s + 1 by omega) huC
  have hsub1 : s + 1 - 1 - 1 = s - 1 := by omega
  have hsub2 : c - (s + 1) + 1 + 1 = c - s + 1 := by
    have h2s : 2 * (s + 1) ≤ c := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp huC
    omega
  simpa [cycleQ, hsub1, hsub2] using hQ

/-- `lem:cycle-arithmetic-consequences` (ii). -/
theorem cycle_arithmetic_consequence_ii {k n c : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n) (hnUpper : n ≤ (5 * k + 2) / 2)
    (hc : c < n) (hc2 : 1 ≤ c / 2) :
    (c / 2 - 1) * (n - c) +
        ((((c / 2 - 1) * min (c / 2) (k + 1) +
          (c - c / 2 + 1) * (k + 1))) / 2) ≤
      h k n := by
  let u := c / 2
  have hQ := cycleQ_le_h hk hn hnUpper hc (show (0 : ℕ) ≤ 1 by omega)
    (show 1 + 0 ≤ u by simpa [u] using hc2) (show u ≤ c / 2 by rfl)
  have hmin : min u (k + 1) ≤ u := min_le_left _ _
  have hmul := Nat.mul_le_mul_left (u - 1) hmin
  have hnum :
      (u - 1) * min u (k + 1) + (c - u + 1) * (k + 1) ≤
        (u - 1) * u + (c - u + 1) * (k + 1) := by omega
  have hdiv :
      ((u - 1) * min u (k + 1) + (c - u + 1) * (k + 1)) / 2 ≤
        ((u - 1) * u + (c - u + 1) * (k + 1)) / 2 :=
    Nat.div_le_div_right hnum
  have htarget :
      (u - 1) * (n - c) +
          (((u - 1) * min u (k + 1) +
            (c - u + 1) * (k + 1)) / 2) ≤
        cycleQ k n c u 0 := by
    simpa [cycleQ] using Nat.add_le_add_left hdiv ((u - 1) * (n - c))
  simpa [u] using htarget.trans hQ

/-- Both conclusions of `lem:cycle-arithmetic-consequences`. -/
theorem cycle_arithmetic_consequences {k n c : ℕ}
    (hk : 2 ≤ k) (hn : k + 2 ≤ n) (hnUpper : n ≤ (5 * k + 2) / 2)
    (hc : c < n) :
    (∀ s, 2 ≤ s → s ≤ c / 2 - 1 →
      s * (n - c) +
          (((s - 1) * s + (c - s + 1) * (k + 1)) / 2) ≤ h k n) ∧
    (1 ≤ c / 2 →
      (c / 2 - 1) * (n - c) +
          ((((c / 2 - 1) * min (c / 2) (k + 1) +
            (c - c / 2 + 1) * (k + 1))) / 2) ≤ h k n) := by
  constructor
  · intro s hs0 hs1
    exact cycle_arithmetic_consequence_i hk hn hnUpper hc hs0 hs1
  · intro hc2
    exact cycle_arithmetic_consequence_ii hk hn hnUpper hc hc2
end Erdos767
