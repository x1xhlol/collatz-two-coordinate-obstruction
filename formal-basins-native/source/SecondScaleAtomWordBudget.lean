import SecondScaleCanonicalLocalClockProbability

set_option autoImplicit false
open Filter Topology

namespace CollatzPassageAtomsSecondScale
open Erdos1135SecondScale.Tao CollatzClockSecondScale

noncomputable def atomWordBudget (B : ℕ) : ℕ :=
  ⌊2 * (taoSection5N0 B : ℝ) + Real.log (B : ℝ) / 1000⌋₊

theorem atomWordBudget_pow_le {B : ℕ} (hB : 1 ≤ B) :
    (2 : ℝ) ^ atomWordBudget B ≤ (B : ℝ) ^ (1 / 4 : ℝ) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hL : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht1 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn := (le_div_iff₀ (show 0 < 10 * Real.log (2 : ℝ) by positivity)).mp
    (taoSection5N0_le_log_div_ten_log_two B)
  have hf : (atomWordBudget B : ℝ) ≤ 2 * (taoSection5N0 B : ℝ) + Real.log (B : ℝ) / 1000 :=
    Nat.floor_le (by positivity)
  have hfm := mul_le_mul_of_nonneg_right hf ht.le
  have htm := mul_le_mul_of_nonneg_left ht1 hL
  have he : Real.log 2 * (atomWordBudget B : ℝ) ≤ Real.log (B : ℝ) * (1 / 4 : ℝ) := by
    nlinarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hBR]
  exact Real.exp_le_exp.mpr he

theorem atomWordBudget_mass_le {B : ℕ} (hB : 1 ≤ B) {mass : ℝ}
    (hmass : (1 / 4 : ℝ) ≤ mass) :
    (2 : ℝ) ^ atomWordBudget B * ((1 : ℝ) / B / mass) ≤
      4 * (B : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hm : 0 < mass := by linarith
  have hrec : (1 : ℝ) / B / mass ≤ 4 / B := by
    apply (div_le_iff₀ hm).mpr
    have hh := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 4 / B by positivity)
    nlinarith [show (4 / (B : ℝ)) * (1 / 4 : ℝ) = 1 / B by ring]
  have hr : (B : ℝ) ^ (1 / 4 : ℝ) / B = (B : ℝ) ^ (-(3 / 4 : ℝ)) := by
    rw [show -(3 / 4 : ℝ) = (1 / 4 : ℝ) - 1 by norm_num,
      Real.rpow_sub hBR, Real.rpow_one]
  calc
    _ ≤ (2 : ℝ) ^ atomWordBudget B * (4 / B) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ ≤ (B : ℝ) ^ (1 / 4 : ℝ) * (4 / B) :=
      mul_le_mul_of_nonneg_right (atomWordBudget_pow_le hB) (by positivity)
    _ = 4 * ((B : ℝ) ^ (1 / 4 : ℝ) / B) := by ring
    _ = _ := by rw [hr]

theorem eventually_atom_total_error_le :
    ∀ᶠ B : ℕ in atTop,
      coarsePrefixError B + 4 * (B : ℝ) ^ (-(3 / 4 : ℝ)) ≤
        5 * (B : ℝ) ^ (-(1 / 12800000 : ℝ)) := by
  filter_upwards [eventually_coarsePrefixError_le_rpow, eventually_ge_atTop (1 : ℕ)] with B hB hB1
  have hpow : (B : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (B : ℝ) ^ (-(1 / 12800000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB1) (by norm_num)
  linarith

end CollatzPassageAtomsSecondScale
