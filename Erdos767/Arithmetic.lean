import Erdos767.Basic

/-!
# Arithmetic lemmas for Erdős Problem 767

The theorem names mention the corresponding labels in
`ErdosProblem767.tex`.
-/

namespace Erdos767

/-- The exact calculation in the sharpness remark following the two lower-bound
constructions.  This is the subtraction-free form of the displayed identity.
-/
theorem sharp_threshold_identity (k : ℕ) (hk : 1 ≤ k) :
    let n := 2 * k + k / 2
    (k + 1) * (n - k - 1) + 1 = k * (n - k) + k / 2 := by
  dsimp
  have h₁ : 2 * k + k / 2 - k - 1 = (k - 1) + k / 2 := by omega
  have h₂ : 2 * k + k / 2 - k = k + k / 2 := by omega
  rw [h₁, h₂]
  nlinarith [Nat.sub_add_cancel hk]

/-- Advancing `n` by one advances a fixed split term by `a`, provided `a ≤ n`.
This is the algebraic core of Claim `claim:Sk-linear-increment` (i).
-/
theorem splitTerm_succ {k m a : ℕ} (ha : a ≤ m) :
    splitTerm k (m + 1) a = splitTerm k m a + a := by
  have hsub : m + 1 - a = (m - a) + 1 := by omega
  simp only [splitTerm, hsub, Nat.mul_add, Nat.mul_one]
  omega

/-- Claim `claim:Sk-linear-increment` (i), with its implicit domain hypotheses made
explicit. -/
theorem p_succ_ge_of_eq_splitTerm {k m a : ℕ}
    (haA : a ∈ A k) (ham : a ≤ m)
    (hmax : p k m = splitTerm k m a) :
    p k m + a ≤ p k (m + 1) := by
  rw [hmax, ← splitTerm_succ ham]
  exact p_ge_splitTerm haA

/-- The numerical assertion in the exceptional case of
Lemma `lem:small-c-arithmetic`: its left side is `17 = h_3(8) + 1`.
-/
theorem small_c_exception_value :
    (6 / 2) * (8 - 6) +
        ((((6 / 2) - 1) * (6 / 2) + (6 - 6 / 2 + 1) * (3 + 1)) / 2) =
      17 ∧
    h 3 8 + 1 = 17 := by
  decide

/-- Lemma `lem:small-c-arithmetic`, formalized as a finite, kernel-checked
calculation.  The upper bound `(5*k+2)/2` is
`ceil ((5*k+1)/2)` for natural `k`.
-/
theorem small_c_arithmetic {k n c : ℕ}
    (hk₀ : 2 ≤ k) (hk₁ : k ≤ 6)
    (hn₀ : k + 2 ≤ n) (hn₁ : n ≤ (5 * k + 2) / 2)
    (hc₀ : 2 * ((k + 1) / 2) + 2 ≤ c) (hcn : c < n) (hc₁ : c ≤ 9)
    (hex : ¬(k = 3 ∧ n = 8 ∧ c = 6)) :
    (c / 2) * (n - c) +
        ((((c / 2) - 1) * (c / 2) + (c - c / 2 + 1) * (k + 1)) / 2) ≤
      h k n := by
  interval_cases k <;> interval_cases n <;> interval_cases c <;>
    norm_num at * <;> decide

/-- The `d = 1` calculation used in Lemma `lem:S-terminal`, stated without
integer ceiling notation. -/
theorem terminal_d_one_nonnegative {k n : ℕ}
    (hn : 5 * k + 1 ≤ 2 * n) :
    2 * k + 1 + k / 2 ≤ n := by
  omega

end Erdos767
