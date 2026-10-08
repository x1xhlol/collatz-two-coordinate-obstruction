import Erdos1135Predecessor.ND.PositiveDensity.PredecessorAnalyticSupport

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor
open Erdos1135Predecessor.ND.PositiveDensity

/-- Preserve the native sixth-power mixing estimate when using the terminal
census interface stated with a quadratic denominator. -/
theorem sixth_mixing_as_quadratic {C : ℝ} (_hC : 0 ≤ C)
    (hmix : Tao.syracFineScaleMixingAt 6 C) {m : ℕ} (hm : 1 ≤ m) :
    ndExplicitQuadraticMixingAt ((2 / 3 : ℝ) * C / (m : ℝ) ^ 4) m := by
  intro k hmk
  rw [unitReferenceDensity_fullL1_eq_twoThirds_oscillation hmk]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  calc
    _ ≤ (2 / 3 : ℝ) * (C / (m : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left (hmix k m hm hmk) (by norm_num)
    _ = _ := by field_simp

theorem sixth_power_square_budget {r C : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hbudget : 88 * r * C ≤ (m : ℝ) ^ 6) :
    88 * r * ((2 / 3 : ℝ) * C / (m : ℝ) ^ 4) ≤
      (2 / 3 : ℝ) * (m : ℝ) ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply (mul_le_mul_iff_of_pos_right (show (0 : ℝ) < (m : ℝ) ^ 4 by positivity)).mp
  have hscale := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 2 / 3)
  convert hscale using 1 <;> field_simp

#print axioms sixth_mixing_as_quadratic
#print axioms sixth_power_square_budget

end CollatzCanonical.BoundedInverseSeed
