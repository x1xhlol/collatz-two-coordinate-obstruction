import Mathlib.Analysis.PSeries

/-!
# Shifted Inverse-Power Tails

This scalar leaf bounds the finite reciprocal-power sum produced by shifting
an adjacent-scale telescope.  It contains no Syracuse or high-regime input.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- The shifted reciprocal-square sum is exactly the finite interval consumed
by Mathlib's sharp inverse-square tail estimate. -/
theorem sum_Ico_one_div_succ_sq_le_sub
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ r ∈ Finset.Ico m n,
      1 / (((r + 1 : ℕ) : ℝ) ^ 2)) ≤
      1 / (m : ℝ) - 1 / (n : ℝ) := by
  rw [Finset.sum_Ico_add'
    (fun k : ℕ => 1 / (k : ℝ) ^ 2) m n 1]
  rw [Finset.Ico_add_one_add_one_eq_Ioc]
  simpa only [one_div] using
    (sum_Ioc_inv_sq_le_sub (α := ℝ) (Nat.ne_of_gt hm) hmn)

/-- A positive reciprocal exponent gains one lower-scale power after summing
over a shifted finite interval. -/
theorem sum_Ico_one_div_succ_pow_le
    {A m n : ℕ} (hA : 0 < A) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ r ∈ Finset.Ico m n,
      1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) ≤
      1 / (m : ℝ) ^ A := by
  obtain ⟨B, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hA)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpoint : ∀ r ∈ Finset.Ico m n,
      1 / (((r + 1 : ℕ) : ℝ) ^ (B + 1 + 1)) ≤
        (1 / (m : ℝ) ^ B) *
          (1 / (((r + 1 : ℕ) : ℝ) ^ 2)) := by
    intro r hr
    simp only [Finset.mem_Ico] at hr
    have hmr : m ≤ r + 1 := hr.1.trans (Nat.le_succ r)
    have hmrR : (m : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast hmr
    have hpow : (m : ℝ) ^ B ≤ ((r + 1 : ℕ) : ℝ) ^ B :=
      pow_le_pow_left₀ hmR.le hmrR B
    have hinv : 1 / (((r + 1 : ℕ) : ℝ) ^ B) ≤
        1 / (m : ℝ) ^ B :=
      one_div_le_one_div_of_le (pow_pos hmR B) hpow
    calc
      1 / (((r + 1 : ℕ) : ℝ) ^ (B + 1 + 1)) =
          (1 / (((r + 1 : ℕ) : ℝ) ^ B)) *
            (1 / (((r + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [show B + 1 + 1 = B + 2 by omega, pow_add]
        ring
      _ ≤ (1 / (m : ℝ) ^ B) *
          (1 / (((r + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
  calc
    (∑ r ∈ Finset.Ico m n,
        1 / (((r + 1 : ℕ) : ℝ) ^ (B + 1 + 1))) ≤
        ∑ r ∈ Finset.Ico m n,
          (1 / (m : ℝ) ^ B) *
            (1 / (((r + 1 : ℕ) : ℝ) ^ 2)) := by
      exact Finset.sum_le_sum hpoint
    _ = (1 / (m : ℝ) ^ B) *
        (∑ r ∈ Finset.Ico m n,
          1 / (((r + 1 : ℕ) : ℝ) ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (m : ℝ) ^ B) *
        (1 / (m : ℝ) - 1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_Ico_one_div_succ_sq_le_sub hm hmn) (by positivity)
    _ ≤ (1 / (m : ℝ) ^ B) * (1 / (m : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact sub_le_self _ (by positivity)
      · positivity
    _ = 1 / (m : ℝ) ^ (B + 1) := by
      rw [pow_succ]
      ring

/-- Exponent-one canary: the general estimate reduces to reciprocal squares. -/
theorem sum_Ico_one_div_succ_sq_le
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ r ∈ Finset.Ico m n,
      1 / (((r + 1 : ℕ) : ℝ) ^ 2)) ≤
      1 / (m : ℝ) := by
  simpa using
    sum_Ico_one_div_succ_pow_le
      (A := 1) (m := m) (n := n) (by omega) hm hmn

/-- Empty-interval canary. -/
theorem sum_Ico_one_div_succ_pow_self_le
    {A m : ℕ} (hA : 0 < A) (hm : 1 ≤ m) :
    (∑ r ∈ Finset.Ico m m,
      1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) ≤
      1 / (m : ℝ) ^ A :=
  sum_Ico_one_div_succ_pow_le hA hm (le_refl m)

/-- Singleton-interval canary. -/
theorem sum_Ico_one_div_succ_pow_succ_le
    {A m : ℕ} (hA : 0 < A) (hm : 1 ≤ m) :
    (∑ r ∈ Finset.Ico m (m + 1),
      1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) ≤
      1 / (m : ℝ) ^ A :=
  sum_Ico_one_div_succ_pow_le hA hm (Nat.le_succ m)

/-- Source-cutoff pilot at the first scale of Tao's telescope. -/
theorem sum_Ico_ten_one_div_succ_pow_le
    {A n : ℕ} (hA : 0 < A) (hn : 10 ≤ n) :
    (∑ r ∈ Finset.Ico 10 n,
      1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) ≤
      1 / (10 : ℝ) ^ A :=
  sum_Ico_one_div_succ_pow_le hA (by omega) hn

end

end Tao
end Erdos1135
