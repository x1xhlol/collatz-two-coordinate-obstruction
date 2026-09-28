import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Generic floor-loss bridge for Rhin remainder certificates

This module contains no literal Rhin data.  It turns exact rounded-exponent
cell inequalities into all-natural-index product bounds while retaining a
single explicit loss factor for maxima below one.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

open scoped BigOperators

/-- One-factor floor loss at rounding scale `1000`.  The caller supplies the
upper or lower rounded exponent inequality according to whether the factor
maximum is at least one. -/
private theorem floorPowerBound
    (M : ℝ) (m e n : ℕ)
    (hM : 0 < M)
    (hUpper : 1 ≤ M → 1000 * m ≤ e * n)
    (hLower : M < 1 → e * n ≤ 1000 * m + 1000) :
    (M ^ m) ^ 1000 ≤
      (if M < 1 then M⁻¹ else 1) ^ 1000 * (M ^ e) ^ n := by
  by_cases hSmall : M < 1
  · rw [if_pos hSmall]
    have hPowPos : 0 < M ^ 1000 := pow_pos hM _
    have hRewrite :
        M⁻¹ ^ 1000 * (M ^ e) ^ n = (M ^ e) ^ n / M ^ 1000 := by
      rw [inv_pow, div_eq_mul_inv, mul_comm]
    rw [hRewrite]
    apply (le_div_iff₀ hPowPos).2
    calc
      (M ^ m) ^ 1000 * M ^ 1000 = M ^ (m * 1000) * M ^ 1000 := by
        rw [pow_mul]
      _ = M ^ (m * 1000 + 1000) := by rw [pow_add]
      _ = M ^ (1000 * m + 1000) := by
        congr 2
        omega
      _ ≤ M ^ (e * n) :=
        pow_le_pow_of_le_one hM.le hSmall.le (hLower hSmall)
      _ = (M ^ e) ^ n := by rw [pow_mul]
  · have hLarge : 1 ≤ M := le_of_not_gt hSmall
    rw [if_neg hSmall, one_pow, one_mul]
    rw [← pow_mul, ← pow_mul]
    apply pow_le_pow_right₀ hLarge
    simpa only [Nat.mul_comm] using hUpper hLarge

/-- Product form of `floorPowerBound`, retaining one finite loss constant for
all factors whose cell maximum is below one. -/
private theorem finsetFloorPowerBound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (M : ι → ℝ) (m e : ι → ℕ) (n : ℕ)
    (hM : ∀ i ∈ s, 0 < M i)
    (hUpper : ∀ i ∈ s, 1 ≤ M i → 1000 * m i ≤ e i * n)
    (hLower : ∀ i ∈ s, M i < 1 → e i * n ≤ 1000 * m i + 1000) :
    (∏ i ∈ s, M i ^ m i) ^ 1000 ≤
      (∏ i ∈ s, if M i < 1 then (M i)⁻¹ else 1) ^ 1000 *
        (∏ i ∈ s, M i ^ e i) ^ n := by
  calc
    (∏ i ∈ s, M i ^ m i) ^ 1000 =
        ∏ i ∈ s, (M i ^ m i) ^ 1000 := by
      simp only [Finset.prod_pow]
    _ ≤ ∏ i ∈ s,
        (if M i < 1 then (M i)⁻¹ else 1) ^ 1000 *
          (M i ^ e i) ^ n := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact floorPowerBound (M i) (m i) (e i) n (hM i hi)
          (hUpper i hi) (hLower i hi)
    _ = (∏ i ∈ s, if M i < 1 then (M i)⁻¹ else 1) ^ 1000 *
        (∏ i ∈ s, M i ^ e i) ^ n := by
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]

/-- A checked rounded-exponent cell inequality implies the all-`n` product
estimate, including every natural-floor loss. -/
theorem cellProductBound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (M : ι → ℝ) (m e : ι → ℕ)
    (n : ℕ) (base left : ℝ)
    (hM : ∀ i ∈ s, 0 < M i)
    (hUpper : ∀ i ∈ s, 1 ≤ M i → 1000 * m i ≤ e i * n)
    (hLower : ∀ i ∈ s, M i < 1 → e i * n ≤ 1000 * m i + 1000)
    (hBase : 0 ≤ base) (hLeft : 0 ≤ left)
    (hCell : (∏ i ∈ s, M i ^ e i) ≤ (base * left) ^ 1000) :
    ∏ i ∈ s, M i ^ m i ≤
      (∏ i ∈ s, if M i < 1 then (M i)⁻¹ else 1) *
        (base * left) ^ n := by
  let C : ℝ := ∏ i ∈ s, if M i < 1 then (M i)⁻¹ else 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · exact (inv_pos.mpr (hM i hi)).le
    · norm_num
  have hQ : 0 ≤ ∏ i ∈ s, M i ^ e i := by
    apply Finset.prod_nonneg
    intro i hi
    exact pow_nonneg (hM i hi).le _
  have hP : 0 ≤ ∏ i ∈ s, M i ^ m i := by
    apply Finset.prod_nonneg
    intro i hi
    exact pow_nonneg (hM i hi).le _
  have hTarget : 0 ≤ C * (base * left) ^ n :=
    mul_nonneg hC (pow_nonneg (mul_nonneg hBase hLeft) _)
  have hRaw := finsetFloorPowerBound s M m e n hM hUpper hLower
  have hCellPow :
      (∏ i ∈ s, M i ^ e i) ^ n ≤ ((base * left) ^ 1000) ^ n :=
    pow_le_pow_left₀ hQ hCell n
  have hPowers :
      (∏ i ∈ s, M i ^ m i) ^ 1000 ≤
        (C * (base * left) ^ n) ^ 1000 := by
    calc
      (∏ i ∈ s, M i ^ m i) ^ 1000 ≤
          C ^ 1000 * (∏ i ∈ s, M i ^ e i) ^ n := by
        simpa only [C] using hRaw
      _ ≤ C ^ 1000 * ((base * left) ^ 1000) ^ n :=
        mul_le_mul_of_nonneg_left hCellPow (pow_nonneg hC _)
      _ = (C * (base * left) ^ n) ^ 1000 := by
        rw [mul_pow C ((base * left) ^ n) 1000]
        congr 1
        calc
          ((base * left) ^ 1000) ^ n =
              (base * left) ^ (1000 * n) := (pow_mul _ _ _).symm
          _ = (base * left) ^ (n * 1000) := by rw [Nat.mul_comm]
          _ = ((base * left) ^ n) ^ 1000 := pow_mul _ _ _
  exact (pow_le_pow_iff_left₀ hP hTarget
    (by norm_num : (1000 : ℕ) ≠ 0)).mp hPowers

end

end Rhin
end NumberTheory
end Erdos1135
