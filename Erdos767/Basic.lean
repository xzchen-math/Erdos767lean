import Mathlib

/-!
# Erdős Problem 767: arithmetic definitions

This file formalizes the integer-valued functions from Section 3 of
`ErdosProblem767.tex`.
Natural-number division by `2` is the floor appearing in the paper.
-/

namespace Erdos767

/-- The admissible set `A_k` from the paper. -/
def A (k : ℕ) : Finset ℕ := Finset.Icc ((k + 1) / 2 + 1) (k + 1)

/-- The nearly-regular construction count `t_k(n)`. -/
def t (k n : ℕ) : ℕ := ((k + 1) * n) / 2

/-- The number of edges in the split construction with parameter `a`. -/
def splitTerm (k n a : ℕ) : ℕ :=
  a * (n - a) + (a * (k + 1 - a)) / 2

/-- The best split-construction count `p_k(n)`.

`Finset.sup` returns `0` on an empty set.  In every use in the paper `k ≥ 2`, and
`A k` is nonempty (indeed, it contains `k + 1`).
-/
def p (k n : ℕ) : ℕ := (A k).sup (splitTerm k n)

/-- The comparison function `h_k(n)` from the paper. -/
def h (k n : ℕ) : ℕ :=
  if n ≤ k + 1 then n.choose 2 else max (t k n) (p k n)

@[simp] theorem mem_A_iff {k a : ℕ} :
    a ∈ A k ↔ (k + 1) / 2 + 1 ≤ a ∧ a ≤ k + 1 := by
  simp [A]

@[simp] theorem top_mem_A (k : ℕ) : k + 1 ∈ A k := by
  simp [A]
  omega

theorem p_ge_splitTerm {k n a : ℕ} (ha : a ∈ A k) :
    splitTerm k n a ≤ p k n := by
  exact Finset.le_sup ha

theorem p_ge_terminal (k n : ℕ) :
    (k + 1) * (n - (k + 1)) ≤ p k n := by
  have hle := p_ge_splitTerm (k := k) (n := n) (a := k + 1) (top_mem_A k)
  simpa [splitTerm] using hle

theorem h_eq_max {k n : ℕ} (hn : k + 2 ≤ n) :
    h k n = max (t k n) (p k n) := by
  simp [h]
  omega

theorem t_le_h {k n : ℕ} (hn : k + 2 ≤ n) : t k n ≤ h k n := by
  rw [h_eq_max hn]
  exact le_max_left _ _

theorem p_le_h {k n : ℕ} (hn : k + 2 ≤ n) : p k n ≤ h k n := by
  rw [h_eq_max hn]
  exact le_max_right _ _

end Erdos767
