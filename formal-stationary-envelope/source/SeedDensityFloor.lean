import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed

noncomputable def seedConductorFloor (C r : ℕ) : ℕ :=
  ⌊(88 * (C : ℝ) * (r : ℝ)) ^ (1 / 6 : ℝ)⌋₊

noncomputable def seedMixingDepth (C r : ℕ) : ℕ :=
  seedConductorFloor C r + 1

noncomputable def sixthRootDensityFloor (C r : ℕ) : ℝ :=
  1 / (256 * (r : ℝ) * (3 : ℝ) ^ seedConductorFloor C r)

theorem seedMixingDepth_one_le (C r : ℕ) : 1 ≤ seedMixingDepth C r := by
  unfold seedMixingDepth
  omega

theorem seedConductorFloor_monotone (C : ℕ) : Monotone (seedConductorFloor C) := by
  intro r s hrs
  unfold seedConductorFloor
  apply Nat.floor_mono
  apply Real.rpow_le_rpow (by positivity)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) (by positivity)
  · norm_num

theorem seedMixingDepth_budget (C r : ℕ) :
    88 * (r : ℝ) * (C : ℝ) ≤ (seedMixingDepth C r : ℝ) ^ 6 := by
  let R : ℝ := (88 * (C : ℝ) * (r : ℝ)) ^ (1 / 6 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hdepth : R ≤ (seedMixingDepth C r : ℝ) := by
    simpa only [seedMixingDepth, seedConductorFloor, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one R).le
  have hpow : R ^ 6 = 88 * (C : ℝ) * (r : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 88 * (C : ℝ) * (r : ℝ))]
    norm_num
  calc
    _ = R ^ 6 := by rw [hpow]; ring
    _ ≤ _ := pow_le_pow_left₀ hR hdepth _

theorem sixthRootDensityFloor_pos (C : ℕ) {r : ℕ} (hr : 0 < r) :
    0 < sixthRootDensityFloor C r := by
  unfold sixthRootDensityFloor
  positivity

theorem sixthRootDensityFloor_antitone (C : ℕ) {r s : ℕ} (hr : 0 < r)
    (hrs : r ≤ s) : sixthRootDensityFloor C s ≤ sixthRootDensityFloor C r := by
  have hpow : (3 : ℝ) ^ seedConductorFloor C r ≤ (3 : ℝ) ^ seedConductorFloor C s :=
    pow_le_pow_right₀ (by norm_num) (seedConductorFloor_monotone C hrs)
  have hden : 256 * (r : ℝ) * (3 : ℝ) ^ seedConductorFloor C r ≤
      256 * (s : ℝ) * (3 : ℝ) ^ seedConductorFloor C s :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) (by norm_num))
      hpow (by positivity) (by positivity)
  exact one_div_le_one_div_of_le (by positivity) hden

theorem sixthRootDensityFloor_eq_depth (C : ℕ) {r : ℕ} (hr : 0 < r) :
    sixthRootDensityFloor C r =
      3 / (256 * (r : ℝ) * (3 : ℝ) ^ seedMixingDepth C r) := by
  unfold sixthRootDensityFloor seedMixingDepth
  rw [pow_succ]
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hpne : (3 : ℝ) ^ seedConductorFloor C r ≠ 0 := by positivity
  field_simp

theorem sixthRootDensityFloor_ge_exp (C : ℕ) {r : ℕ} (hr : 0 < r) :
    Real.exp (-Real.log 3 * (88 * (C : ℝ) * (r : ℝ)) ^ (1 / 6 : ℝ)) /
      (256 * (r : ℝ)) ≤ sixthRootDensityFloor C r := by
  let R : ℝ := (88 * (C : ℝ) * (r : ℝ)) ^ (1 / 6 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hfloor : (seedConductorFloor C r : ℝ) ≤ R := Nat.floor_le hR
  have hpow : (3 : ℝ) ^ seedConductorFloor C r ≤ (3 : ℝ) ^ R := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hfloor
  have hinv : 1 / (3 : ℝ) ^ R ≤ 1 / (3 : ℝ) ^ seedConductorFloor C r :=
    one_div_le_one_div_of_le (by positivity) hpow
  have he : 1 / (3 : ℝ) ^ R = Real.exp (-Real.log 3 * R) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [he] at hinv
  have h := div_le_div_of_nonneg_right hinv (by positivity : 0 ≤ 256 * (r : ℝ))
  convert h using 1
  unfold sixthRootDensityFloor
  ring

#print axioms seedConductorFloor
#print axioms seedMixingDepth
#print axioms sixthRootDensityFloor
#print axioms seedMixingDepth_one_le
#print axioms seedConductorFloor_monotone
#print axioms seedMixingDepth_budget
#print axioms sixthRootDensityFloor_pos
#print axioms sixthRootDensityFloor_antitone
#print axioms sixthRootDensityFloor_eq_depth
#print axioms sixthRootDensityFloor_ge_exp

end CollatzCanonical.BoundedInverseSeed
