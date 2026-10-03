import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed

noncomputable def powerConductorFloor (p : ℕ) (C : ℝ) (r : ℕ) : ℕ :=
  ⌊(88 * (C : ℝ) * (r : ℝ)) ^ (1 / (p : ℝ))⌋₊

noncomputable def powerMixingDepth (p : ℕ) (C : ℝ) (r : ℕ) : ℕ :=
  powerConductorFloor p C r + 1

noncomputable def powerDensityFloor (p : ℕ) (C : ℝ) (r : ℕ) : ℝ :=
  1 / (256 * (r : ℝ) * (3 : ℝ) ^ powerConductorFloor p C r)

theorem powerMixingDepth_one_le (p : ℕ) (C : ℝ) (r : ℕ) : 1 ≤ powerMixingDepth p C r := by
  unfold powerMixingDepth
  omega

theorem powerConductorFloor_monotone (p : ℕ) (C : ℝ) (hC : 0 ≤ C) : Monotone (powerConductorFloor p C) := by
  intro r s hrs
  unfold powerConductorFloor
  apply Nat.floor_mono
  apply Real.rpow_le_rpow (by positivity)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) (by positivity)
  · norm_num

theorem powerMixingDepth_budget (p : ℕ) (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C) (r : ℕ) :
    88 * (r : ℝ) * (C : ℝ) ≤ (powerMixingDepth p C r : ℝ) ^ p := by
  let R : ℝ := (88 * (C : ℝ) * (r : ℝ)) ^ (1 / (p : ℝ))
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hdepth : R ≤ (powerMixingDepth p C r : ℝ) := by
    simpa only [powerMixingDepth, powerConductorFloor, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one R).le
  have hpow : R ^ p = 88 * (C : ℝ) * (r : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 88 * (C : ℝ) * (r : ℝ))]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
    rw [one_div_mul_cancel hpR, Real.rpow_one]
  calc
    _ = R ^ p := by rw [hpow]; ring
    _ ≤ _ := pow_le_pow_left₀ hR hdepth _

theorem powerDensityFloor_pos (p : ℕ) (C : ℝ) {r : ℕ} (hr : 0 < r) :
    0 < powerDensityFloor p C r := by
  unfold powerDensityFloor
  positivity

theorem powerDensityFloor_antitone (p : ℕ) (C : ℝ) (hC : 0 ≤ C) {r s : ℕ} (hr : 0 < r)
    (hrs : r ≤ s) : powerDensityFloor p C s ≤ powerDensityFloor p C r := by
  have hpow : (3 : ℝ) ^ powerConductorFloor p C r ≤ (3 : ℝ) ^ powerConductorFloor p C s :=
    pow_le_pow_right₀ (by norm_num) (powerConductorFloor_monotone p C hC hrs)
  have hden : 256 * (r : ℝ) * (3 : ℝ) ^ powerConductorFloor p C r ≤
      256 * (s : ℝ) * (3 : ℝ) ^ powerConductorFloor p C s :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) (by norm_num))
      hpow (by positivity) (by positivity)
  exact one_div_le_one_div_of_le (by positivity) hden

theorem powerDensityFloor_eq_depth (p : ℕ) (C : ℝ) {r : ℕ} (hr : 0 < r) :
    powerDensityFloor p C r =
      3 / (256 * (r : ℝ) * (3 : ℝ) ^ powerMixingDepth p C r) := by
  unfold powerDensityFloor powerMixingDepth
  rw [pow_succ]
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hpne : (3 : ℝ) ^ powerConductorFloor p C r ≠ 0 := by positivity
  field_simp

theorem powerDensityFloor_ge_exp (p : ℕ) (C : ℝ) (hC : 0 ≤ C) {r : ℕ} (hr : 0 < r) :
    Real.exp (-Real.log 3 * (88 * (C : ℝ) * (r : ℝ)) ^ (1 / (p : ℝ))) /
      (256 * (r : ℝ)) ≤ powerDensityFloor p C r := by
  let R : ℝ := (88 * (C : ℝ) * (r : ℝ)) ^ (1 / (p : ℝ))
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hfloor : (powerConductorFloor p C r : ℝ) ≤ R := Nat.floor_le hR
  have hpow : (3 : ℝ) ^ powerConductorFloor p C r ≤ (3 : ℝ) ^ R := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hfloor
  have hinv : 1 / (3 : ℝ) ^ R ≤ 1 / (3 : ℝ) ^ powerConductorFloor p C r :=
    one_div_le_one_div_of_le (by positivity) hpow
  have he : 1 / (3 : ℝ) ^ R = Real.exp (-Real.log 3 * R) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [he] at hinv
  have h := div_le_div_of_nonneg_right hinv (by positivity : 0 ≤ 256 * (r : ℝ))
  convert h using 1
  unfold powerDensityFloor
  ring

#print axioms powerConductorFloor
#print axioms powerMixingDepth
#print axioms powerDensityFloor
#print axioms powerMixingDepth_one_le
#print axioms powerConductorFloor_monotone
#print axioms powerMixingDepth_budget
#print axioms powerDensityFloor_pos
#print axioms powerDensityFloor_antitone
#print axioms powerDensityFloor_eq_depth
#print axioms powerDensityFloor_ge_exp

end CollatzCanonical.BoundedInverseSeed
