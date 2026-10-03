import Erdos1135Predecessor.ND.PositiveDensity.PredecessorAnalyticSupport

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor Erdos1135Predecessor.ND.PositiveDensity

theorem power_mixing_as_quadratic {p : ℕ} {C : ℝ}
    (hmix : Tao.syracFineScaleMixingAt p C) {m : ℕ} (hm : 1 ≤ m) :
    ndExplicitQuadraticMixingAt
      ((2 / 3 : ℝ) * C * (m : ℝ) ^ 2 / (m : ℝ) ^ p) m := by
  intro k hmk
  rw [unitReferenceDensity_fullL1_eq_twoThirds_oscillation hmk]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  calc
    _ ≤ (2 / 3 : ℝ) * (C / (m : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left (hmix k m hm hmk) (by norm_num)
    _ = _ := by field_simp

theorem power_mixing_square_budget {r C : ℝ} {m p : ℕ} (hm : 1 ≤ m)
    (hbudget : 88 * r * C ≤ (m : ℝ) ^ p) :
    88 * r * ((2 / 3 : ℝ) * C * (m : ℝ) ^ 2 / (m : ℝ) ^ p) ≤
      (2 / 3 : ℝ) * (m : ℝ) ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply (mul_le_mul_iff_of_pos_right (show (0 : ℝ) < (m : ℝ) ^ p by positivity)).mp
  have hscale := mul_le_mul_of_nonneg_left hbudget
    (show (0 : ℝ) ≤ (2 / 3 : ℝ) * (m : ℝ) ^ 2 by positivity)
  convert hscale using 1
  field_simp

#print axioms power_mixing_as_quadratic
#print axioms power_mixing_square_budget

end CollatzCanonical.BoundedInverseSeed
