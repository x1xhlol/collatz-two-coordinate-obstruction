import ClockScaleLadder

open Filter
open scoped BigOperators Topology

namespace CollatzClockAudit
open Erdos1135.Tao

noncomputable def clockLadderFailureBudget (C c M : ℝ) (j : ℕ) : ℝ :=
  200000 * (Real.log (clockScale M j)) ^ (-(1 / 10 : ℝ)) +
    (∑ i ∈ Finset.range j,
      (400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) +
        ∑ r ∈ Finset.Ico (i + 1) j, C * (Real.log (clockScale M r)) ^ (-c))) +
    200000 * M ^ (-(1 / 12800000 : ℝ)) +
    ∑ r ∈ Finset.range j, C * (Real.log (clockScale M r)) ^ (-c)

noncomputable def clockLadderFailureCoefficient (C c : ℝ) : ℝ :=
  400000 / (1 - taoAlpha ^ (-(1 / 10 : ℝ))) +
    C / (1 - taoAlpha ^ (-c)) ^ 2 + C / (1 - taoAlpha ^ (-c))

noncomputable def clockLadderFailureEnvelope (C c M : ℝ) : ℝ :=
  clockLadderFailureCoefficient C c * (Real.log M) ^ (-(min c (1 / 10 : ℝ))) +
    200000 * M ^ (-(1 / 12800000 : ℝ))

theorem clockLadderFailureBudget_le_envelope {C c M : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : Real.exp 1 ≤ M) (j : ℕ) :
    clockLadderFailureBudget C c M j ≤ clockLadderFailureEnvelope C c M := by
  have hMp : 0 < M := (Real.exp_pos 1).trans_le hM
  have hL : 1 ≤ Real.log M := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hM
  have hLp : 0 < Real.log M := by linarith
  have hshift :
      (∑ i ∈ Finset.Ico 1 (j + 1),
        (400000 * (Real.log M * taoAlpha ^ (i - 1)) ^ (-(1 / 10 : ℝ)) +
          ∑ r ∈ Finset.Ico i j, C * (Real.log M * taoAlpha ^ r) ^ (-c))) =
      ∑ i ∈ Finset.range j,
        (400000 * (Real.log M * taoAlpha ^ i) ^ (-(1 / 10 : ℝ)) +
          ∑ r ∈ Finset.Ico (i + 1) j, C * (Real.log M * taoAlpha ^ r) ^ (-c)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.one_add, Nat.succ_sub_one]
  have hclock := geometric_nested_stage_budget hL taoAlpha_one_lt hc
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) ≤ 400000) hC j
  rw [hshift] at hclock
  have htop :
      200000 * (Real.log M * taoAlpha ^ j) ^ (-(1 / 10 : ℝ)) ≤
        400000 * (Real.log M * taoAlpha ^ j) ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by norm_num)
      (Real.rpow_nonneg (mul_nonneg hLp.le (pow_nonneg taoAlpha_pos.le j)) _)
  have hclock' := (add_le_add htop le_rfl).trans hclock
  have htail : (∑ r ∈ Finset.range j, C * (Real.log M * taoAlpha ^ r) ^ (-c)) ≤
      C / (1 - taoAlpha ^ (-c)) * (Real.log M) ^ (-c) := by
    simpa only [Nat.Ico_zero_eq_range] using
      geometric_decay_interval_le_bottom hLp taoAlpha_one_lt hc hC 0 j
  have hden : 0 ≤ C / (1 - taoAlpha ^ (-c)) := by
    exact div_nonneg hC (sub_nonneg.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg taoAlpha_one_lt (by linarith)).le)
  have hpower : (Real.log M) ^ (-c) ≤ (Real.log M) ^ (-(min c (1 / 10 : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left _ _))
  have htail' := htail.trans (mul_le_mul_of_nonneg_left hpower hden)
  unfold clockLadderFailureBudget clockLadderFailureEnvelope clockLadderFailureCoefficient
  simp only [clockScale_log hMp]
  have h := add_le_add (add_le_add hclock' (le_refl (200000 * M ^ (-(1 / 12800000 : ℝ))))) htail'
  nlinarith

theorem clockLadderFailureEnvelope_tendsto_zero {C c : ℝ} (hc : 0 < c) :
    Tendsto (clockLadderFailureEnvelope C c) atTop (𝓝 0) := by
  have hp : 0 < min c (1 / 10 : ℝ) := lt_min hc (by norm_num)
  have hlog : Tendsto (fun M : ℝ =>
      clockLadderFailureCoefficient C c * (Real.log M) ^ (-(min c (1 / 10 : ℝ))))
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hp).comp Real.tendsto_log_atTop).const_mul
      (clockLadderFailureCoefficient C c)
    simpa only [Function.comp_def, mul_zero] using h
  have hlanding : Tendsto (fun M : ℝ => 200000 * M ^ (-(1 / 12800000 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 12800000)).const_mul (200000 : ℝ)
    simpa only [mul_zero] using h
  simpa only [clockLadderFailureEnvelope, add_zero] using hlog.add hlanding

theorem eventually_clockLadderFailureBudget_le {C c ε : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ M : ℝ in atTop, ∀ j : ℕ, clockLadderFailureBudget C c M j ≤ ε := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    (clockLadderFailureEnvelope_tendsto_zero (C := C) hc).eventually_le_const hε]
      with M hM henv
  intro j
  exact (clockLadderFailureBudget_le_envelope hC hc hM j).trans henv

end CollatzClockAudit
