import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

theorem eventually_negative_power_le_log_power {p : ℝ} (hp : p < 0) (c : ℝ) :
    ∀ᶠ x : ℝ in atTop, x ^ p ≤ (Real.log x) ^ (-c) := by
  have h := (isLittleO_log_rpow_rpow_atTop c (neg_pos.mpr hp)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl0.le _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx
  have hi := inv_anti₀ (Real.rpow_pos_of_pos hl0 _) hx
  simpa only [← Real.rpow_neg hx0.le, ← Real.rpow_neg hl0.le, neg_neg] using hi

theorem logarithmic_rate_exponent_weaken {x c d : ℝ} (hx : 1 ≤ Real.log x)
    (hcd : c ≤ d) : (Real.log x) ^ (-d) ≤ (Real.log x) ^ (-c) := by
  exact Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hcd)

#print axioms eventually_negative_power_le_log_power

end CollatzCanonical.NativeTao
