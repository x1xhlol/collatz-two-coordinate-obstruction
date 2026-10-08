import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace CollatzResearch

def twoThreeLocalWeight (q : ℚ) : ℚ :=
  |q| * padicNorm 2 q * padicNorm 3 q

theorem twoThreeLocalWeight_nonneg (q : ℚ) : 0 ≤ twoThreeLocalWeight q := by
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (padicNorm.nonneg _)) (padicNorm.nonneg _)

theorem twoThreeLocalWeight_mul (q r : ℚ) :
    twoThreeLocalWeight (q * r) = twoThreeLocalWeight q * twoThreeLocalWeight r := by
  simp only [twoThreeLocalWeight, abs_mul, padicNorm.mul]
  ring

theorem twoThreeLocalWeight_one : twoThreeLocalWeight 1 = 1 := by
  simp [twoThreeLocalWeight]

theorem twoThreeLocalWeight_pow (q : ℚ) (k : ℕ) :
    twoThreeLocalWeight (q ^ k) = twoThreeLocalWeight q ^ k := by
  induction k with
  | zero => simp [twoThreeLocalWeight_one]
  | succ k ih => rw [pow_succ, twoThreeLocalWeight_mul, ih, pow_succ]

theorem twoThreeLocalWeight_two : twoThreeLocalWeight 2 = 1 := by
  have h : padicNorm 3 (2 : ℚ) = 1 :=
    padicNorm.padicNorm_of_prime_of_ne (p := 3) (q := 2) (by decide)
  have h2 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ :=
    padicNorm.padicNorm_p (p := 2) (by decide)
  rw [twoThreeLocalWeight, h, h2]
  norm_num

theorem twoThreeLocalWeight_three : twoThreeLocalWeight 3 = 1 := by
  have h : padicNorm 2 (3 : ℚ) = 1 :=
    padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by decide)
  have h3 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ :=
    padicNorm.padicNorm_p (p := 3) (by decide)
  rw [twoThreeLocalWeight, h, h3]
  norm_num

theorem twoThreeLocalWeight_int_le (z : ℤ) : twoThreeLocalWeight z ≤ |(z : ℚ)| := by
  calc
    twoThreeLocalWeight z ≤ |(z : ℚ)| * 1 * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (padicNorm.of_int z) (abs_nonneg _)
      · exact padicNorm.of_int z
      · exact padicNorm.nonneg _
      · positivity
    _ = |(z : ℚ)| := by ring

theorem twoThreeLocalWeight_carry (z : ℤ) (p s : ℕ) :
    twoThreeLocalWeight ((z : ℚ) * 2 ^ p * 3 ^ s) ≤ |(z : ℚ)| := by
  simpa only [twoThreeLocalWeight_mul, twoThreeLocalWeight_pow,
    twoThreeLocalWeight_two, twoThreeLocalWeight_three, one_pow, mul_one]
    using twoThreeLocalWeight_int_le z

theorem padicNorm_two_pow (D : ℕ) : padicNorm 2 ((2 : ℚ) ^ D) = ((2 : ℚ) ^ D)⁻¹ := by
  induction D with
  | zero => simp
  | succ D ih =>
      have h2 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ :=
        padicNorm.padicNorm_p (p := 2) (by decide)
      rw [pow_succ, padicNorm.mul, ih, mul_inv_rev, h2]
      ring

theorem trapHead_padic_product_le (a : ℤ) (D : ℕ) :
    padicNorm 2 ((2 : ℚ) ^ D * a) * padicNorm 3 ((2 : ℚ) ^ D * a)
      ≤ ((2 : ℚ) ^ D)⁻¹ := by
  have h3 : padicNorm 3 ((2 : ℚ) ^ D * a) ≤ 1 := by
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using
      (padicNorm.of_int (p := 3) ((2 : ℤ) ^ D * a))
  calc
    _ ≤ padicNorm 2 ((2 : ℚ) ^ D * a) * 1 :=
      mul_le_mul_of_nonneg_left h3 (padicNorm.nonneg _)
    _ ≤ ((2 : ℚ) ^ D)⁻¹ := by
      rw [mul_one, padicNorm.mul, padicNorm_two_pow]
      exact mul_le_of_le_one_right (by positivity) (padicNorm.of_int a)

def trapLocalProduct {t : ℕ} (b : ℚ) (x : Fin (t + 1) → ℚ) : ℚ :=
  (|b| * ∏ i : Fin t, |x i.succ|) *
    (∏ i, padicNorm 2 (x i)) * (∏ i, padicNorm 3 (x i))

theorem trapLocalProduct_split {t : ℕ} (b x0 : ℚ) (y : Fin t → ℚ) :
    trapLocalProduct b (Fin.cases x0 y) =
      |b| * (padicNorm 2 x0 * padicNorm 3 x0) * ∏ i, twoThreeLocalWeight (y i) := by
  simp only [trapLocalProduct, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ,
    twoThreeLocalWeight, Finset.prod_mul_distrib]
  ring

theorem trapLocalProduct_le_carry_product {t : ℕ} (a : ℤ) (b : ℚ) (D : ℕ)
    (z : Fin t → ℤ) (p s : Fin t → ℕ) :
    trapLocalProduct b
      (Fin.cases ((2 : ℚ) ^ D * a) (fun i => (z i : ℚ) * 2 ^ p i * 3 ^ s i))
      ≤ (∏ i, |(z i : ℚ)|) * |b| / 2 ^ D := by
  rw [trapLocalProduct_split]
  calc
    _ ≤ |b| * ((2 : ℚ) ^ D)⁻¹ * ∏ i, |(z i : ℚ)| := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (trapHead_padic_product_le a D) (abs_nonneg _)
      · exact Finset.prod_le_prod₀ (fun i _ => twoThreeLocalWeight_nonneg _)
          (fun i _ => twoThreeLocalWeight_carry (z i) (p i) (s i))
      · exact Finset.prod_nonneg (fun i _ => twoThreeLocalWeight_nonneg _)
      · positivity
    _ = _ := by ring

theorem trapLocalProduct_real_le_carry_product {t : ℕ} (a : ℤ) (b : ℚ) (D : ℕ)
    (z : Fin t → ℤ) (p s : Fin t → ℕ) :
    (trapLocalProduct b
      (Fin.cases ((2 : ℚ) ^ D * a) (fun i => (z i : ℚ) * 2 ^ p i * 3 ^ s i)) : ℝ)
      ≤ (∏ i, |(z i : ℝ)|) * |(b : ℝ)| / 2 ^ D := by
  exact_mod_cast trapLocalProduct_le_carry_product a b D z p s

end CollatzResearch

#print axioms CollatzResearch.trapLocalProduct_le_carry_product
#print axioms CollatzResearch.trapLocalProduct_real_le_carry_product
