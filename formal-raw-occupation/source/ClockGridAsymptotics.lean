import AlignedLadderOccupation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open CollatzClockAudit

theorem commonBottomClockError_div_log_tendsto_zero (M : ℝ) (B : ℕ) :
    Tendsto (fun R : ℝ => commonBottomClockError M R B / Real.log R)
      atTop (𝓝 0) := by
  have hp : Tendsto (fun R : ℝ => (Real.log R) ^ (3 / 5 : ℝ) / Real.log R)
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hlog : 0 < Real.log R := Real.log_pos hR
    simp only [Function.comp_apply]
    rw [show -(2 / 5 : ℝ) = (3 / 5 : ℝ) - 1 by norm_num,
      Real.rpow_sub hlog, Real.rpow_one]
  have hi : Tendsto (fun R : ℝ => (Real.log R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hconst := hi.const_mul ((boundedBarrierRemainder M B : ℝ) +
    |Real.log (B : ℝ) / clockDrift|)
  have hsum := (hp.const_mul globalClockErrorConstant).add hconst
  convert hsum using 1
  · ext R
    unfold commonBottomClockError
    ring
  · ring

/-- One strict exponent margin absorbs all finite clock errors and the
additive one in every height on a fixed grid. -/
theorem clock_grid_uniform_growth_budget {a d : ℝ} (ha : 0 ≤ a)
    (hmargin : a + Real.log (3 / 2 : ℝ) * d / clockDrift < 1)
    (M : ℝ) (B : ℕ) :
    ∀ᶠ R : ℝ in atTop,
      (3 / 2 : ℝ) ^ (d * Real.log R / clockDrift + 2 * commonBottomClockError M R B) *
        (R ^ a + 1) ≤ R + 1 := by
  have hi : Tendsto (fun R : ℝ => Real.log 2 / Real.log R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (Real.log 2)
  have he := commonBottomClockError_div_log_tendsto_zero M B
  have hlim : Tendsto
      (fun R : ℝ => Real.log 2 / Real.log R + a + Real.log (3 / 2 : ℝ) *
        (d / clockDrift + 2 * (commonBottomClockError M R B / Real.log R)))
      atTop (𝓝 (a + Real.log (3 / 2 : ℝ) * d / clockDrift)) := by
    simpa only [mul_zero, add_zero, zero_add, mul_div_assoc] using
      (hi.add_const a).add
        (((he.const_mul 2).const_add (d / clockDrift)).const_mul (Real.log (3 / 2 : ℝ)))
  filter_upwards [hlim.eventually_lt_const hmargin,
    eventually_gt_atTop (1 : ℝ)] with R hsmall hR
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hexp : Real.log 2 + a * Real.log R + Real.log (3 / 2 : ℝ) *
      (d * Real.log R / clockDrift + 2 * commonBottomClockError M R B) ≤ Real.log R := by
    have hid : Real.log 2 / Real.log R + a + Real.log (3 / 2 : ℝ) *
        (d / clockDrift + 2 * (commonBottomClockError M R B / Real.log R)) =
        (Real.log 2 + a * Real.log R + Real.log (3 / 2 : ℝ) *
          (d * Real.log R / clockDrift + 2 * commonBottomClockError M R B)) /
          Real.log R := by field_simp
    rw [hid] at hsmall
    simpa only [one_mul] using ((div_lt_iff₀ hlog).mp hsmall).le
  have hone : (1 : ℝ) ≤ R ^ a := Real.one_le_rpow hR.le ha
  have hid : (3 / 2 : ℝ) ^ (d * Real.log R / clockDrift +
      2 * commonBottomClockError M R B) * (2 * R ^ a) =
      Real.exp (Real.log 2 + a * Real.log R + Real.log (3 / 2 : ℝ) *
        (d * Real.log R / clockDrift + 2 * commonBottomClockError M R B)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
      Real.rpow_def_of_pos (by linarith : 0 < R), Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [mul_comm a (Real.log R)]
    ring
  calc
    (3 / 2 : ℝ) ^ (d * Real.log R / clockDrift + 2 * commonBottomClockError M R B) *
        (R ^ a + 1) ≤
      (3 / 2 : ℝ) ^ (d * Real.log R / clockDrift + 2 * commonBottomClockError M R B) *
        (2 * R ^ a) := by gcongr; linarith
    _ = _ := hid
    _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hexp
    _ ≤ R + 1 := by rw [Real.exp_log (by linarith : 0 < R)]; linarith

#print axioms commonBottomClockError_div_log_tendsto_zero
#print axioms clock_grid_uniform_growth_budget

end CollatzCanonical.RawOccupation
