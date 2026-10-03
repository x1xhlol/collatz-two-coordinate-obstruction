import UniformAlignedOccupationLower
import ClockGridAsymptotics

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open CollatzClockAudit Erdos1135.Tao

theorem finiteOccupationLowerValue_div_log_tendsto
    (P theta M a : ℝ) (B : ℕ) (ha : 0 ≤ a) :
    Tendsto (fun R : ℕ => finiteOccupationLowerValue P theta M R B ((R : ℝ) ^ a) /
      Real.log (R : ℝ)) atTop
      (𝓝 (max 0 (1 - P * M ^ (theta - 1)) * (a / clockDrift))) := by
  let beta := max 0 (1 - P * M ^ (theta - 1))
  have hbeta : 0 ≤ beta := le_max_left _ _
  have hbase : 0 ≤ beta * (a / clockDrift) :=
    mul_nonneg hbeta (div_nonneg ha clockDrift_pos.le)
  have he := (commonBottomClockError_div_log_tendsto_zero M B).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop)
  have hl := (tendsto_const_nhds (x := (0 : ℝ))).max
    (((tendsto_const_nhds (x := a / clockDrift)).sub he).const_mul beta)
  simp only [sub_zero, max_eq_right hbase] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with R hR
  have hR1 : 1 < (R : ℝ) := by exact_mod_cast (show 1 < R by omega)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  unfold finiteOccupationLowerValue
  rw [← max_div_div_right hlog.le, zero_div,
    Real.log_rpow (by linarith : 0 < (R : ℝ))]
  congr 1
  dsimp only [beta, Function.comp_apply]
  field_simp

theorem preBarrier_weight_lower_tendsto_one (P theta : ℝ) (htheta : theta < 1) :
    Tendsto (fun M : ℝ => max 0 (1 - P * M ^ (theta - 1))) atTop (𝓝 1) := by
  have hp : Tendsto (fun M : ℝ => M ^ (theta - 1)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (sub_pos.mpr htheta) using 1
    ext M
    congr 1
    ring
  simpa only [mul_zero, sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using
    (tendsto_const_nhds (x := (0 : ℝ))).max ((hp.const_mul P).const_sub 1)

theorem finiteOccupationLower_coefficient_tendsto
    (P theta C c a : ℝ) (n : ℕ) (htheta : theta < 1) (hc : 0 < c) :
    Tendsto (fun M : ℝ => max 0 (1 - P * M ^ (theta - 1)) * (a / clockDrift) *
      (1 - 2 * (n + 2 : ℕ) * clockLadderFailureEnvelope C c M * taoAlpha))
      atTop (𝓝 (a / clockDrift)) := by
  have hb := (preBarrier_weight_lower_tendsto_one P theta htheta).mul_const (a / clockDrift)
  have hf := ((clockLadderFailureEnvelope_tendsto_zero (C := C) hc).const_mul
    ((2 : ℝ) * (n + 2 : ℕ))).mul_const taoAlpha
  simpa only [one_mul, mul_zero, zero_mul, sub_zero, mul_one] using hb.mul (hf.const_sub 1)

#print axioms finiteOccupationLowerValue_div_log_tendsto
#print axioms preBarrier_weight_lower_tendsto_one
#print axioms finiteOccupationLower_coefficient_tendsto

end CollatzCanonical.RawOccupation
