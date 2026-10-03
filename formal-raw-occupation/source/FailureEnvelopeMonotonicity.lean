import ClockLadderFailureBudget

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit

theorem clock_failure_coefficient_nonneg {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    0 ≤ clockLadderFailureCoefficient C c := by
  have hdc : 0 < 1 - taoAlpha ^ (-c) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg taoAlpha_one_lt (neg_neg_of_pos hc))
  have hdt : 0 < 1 - taoAlpha ^ (-(1 / 10 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg taoAlpha_one_lt (by norm_num))
  unfold clockLadderFailureCoefficient
  positivity

theorem clock_failure_envelope_nonneg {C c M : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 ≤ M) :
    0 ≤ clockLadderFailureEnvelope C c M := by
  have hcoef := clock_failure_coefficient_nonneg hC hc
  have hlog := Real.log_nonneg hM
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  unfold clockLadderFailureEnvelope
  positivity

theorem clock_failure_envelope_antitone {C c M m : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMm : M ≤ m) :
    clockLadderFailureEnvelope C c m ≤ clockLadderFailureEnvelope C c M := by
  have hp : 0 < min c (1 / 10 : ℝ) := lt_min hc (by norm_num)
  have hlog := Real.rpow_le_rpow_of_nonpos (Real.log_pos hM)
    (Real.log_le_log (by linarith) hMm) (neg_nonpos.mpr hp.le)
  have hlanding := Real.rpow_le_rpow_of_nonpos (show 0 < M by linarith) hMm
    (by norm_num : -(1 / 12800000 : ℝ) ≤ 0)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hlog (clock_failure_coefficient_nonneg hC hc))
    (mul_le_mul_of_nonneg_left hlanding (by norm_num))

#print axioms clock_failure_coefficient_nonneg
#print axioms clock_failure_envelope_nonneg
#print axioms clock_failure_envelope_antitone

end CollatzCanonical.RawOccupation
