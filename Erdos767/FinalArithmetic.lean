import Erdos767.Basic

/-! Signed split terms for the full domain of final-paper Claim 5.1(i). -/

namespace Erdos767.FinalPaper

/-- Integer subtraction is essential when `n < a`. The constant term is
nonnegative for admissible `a`, so natural division computes its floor. -/
def splitTermInt (k n a : ℕ) : ℤ :=
  (a : ℤ) * ((n : ℤ) - a) + (a * (k + 1 - a) / 2 : ℕ)

/-- The signed maximum `J_k(n)` on the whole paper domain `n ≥ 1`. -/
def JInt (k n : ℕ) : ℤ :=
  (A k).sup' ⟨k + 1, top_mem_A k⟩ (splitTermInt k n)

theorem splitTermInt_eq_nat {k n a : ℕ} (ha : a ≤ n) :
    splitTermInt k n a = (splitTerm k n a : ℤ) := by
  simp [splitTermInt, splitTerm, Nat.cast_sub ha]

/-- Signed and natural maxima coincide throughout the main theorem range. -/
theorem JInt_eq_nat {k n : ℕ} (hn : k + 1 ≤ n) :
    JInt k n = (p k n : ℤ) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    rw [splitTermInt_eq_nat ((mem_A_iff.mp ha).2.trans hn)]
    exact_mod_cast p_ge_splitTerm ha
  · obtain ⟨a, ha, hmax⟩ :=
      Finset.exists_mem_eq_sup (A k) (⟨k + 1, top_mem_A k⟩ : (A k).Nonempty)
        (splitTerm k n)
    change p k n = splitTerm k n a at hmax
    rw [hmax, ← splitTermInt_eq_nat ((mem_A_iff.mp ha).2.trans hn)]
    exact Finset.le_sup' (splitTermInt k n) ha

theorem splitTermInt_succ (k m a : ℕ) :
    splitTermInt k (m + 1) a = splitTermInt k m a + a := by
  simp only [splitTermInt, Nat.cast_add, Nat.cast_one]
  ring

/-- Final Claim 5.1(i), including `m < a`, with no truncation premise. -/
theorem claim_5_1_i_signed {k m a : ℕ} (ha : a ∈ A k)
    (hmax : JInt k m = splitTermInt k m a) :
    JInt k m + a ≤ JInt k (m + 1) := by
  rw [hmax, ← splitTermInt_succ]
  exact Finset.le_sup' (splitTermInt k (m + 1)) ha

end Erdos767.FinalPaper
