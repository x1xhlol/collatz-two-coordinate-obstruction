import GlobalClockGoodEvent

namespace CollatzClockAudit
open Erdos1135.Tao
open scoped BigOperators

noncomputable def globalClockErrorConstant : ℝ :=
  60 * (taoAlpha ^ (3 / 5 : ℝ) / (taoAlpha ^ (3 / 5 : ℝ) - 1))

def globalBarrierClockEvent (M : ℝ) : Set TaoOddNat :=
  {q | ∃ τ, syracuseFirstHitAtMostReal M q.1 τ ∧
    |(τ : ℝ) - (Real.log (q.1 : ℝ) - Real.log M) / clockDrift| ≤
      globalClockErrorConstant * (Real.log (q.1 : ℝ)) ^ (3 / 5 : ℝ) ∧
    M ^ (1 / 2 : ℝ) < ((syracuse^[τ]) q.1 : ℝ)}

theorem globalClockErrorConstant_pos : 0 < globalClockErrorConstant := by
  have ha : 1 < taoAlpha ^ (3 / 5 : ℝ) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt taoAlpha_one_lt (by norm_num : (0 : ℝ) < 3 / 5)
  unfold globalClockErrorConstant
  exact mul_pos (by norm_num) (div_pos (by linarith) (by linarith))

theorem global_clock_stage_error_le_source {M : ℝ} {q : ℕ} (hM : 1 ≤ M) (j : ℕ)
    (hq : clockScale M j ≤ (q : ℝ)) :
    20 * (Real.log (clockScale M j)) ^ (3 / 5 : ℝ) +
      (∑ i ∈ Finset.range j, 40 * (Real.log (clockScale M (i + 1))) ^ (3 / 5 : ℝ)) ≤
        globalClockErrorConstant * (Real.log (q : ℝ)) ^ (3 / 5 : ℝ) := by
  let f := fun i => (Real.log (clockScale M i)) ^ (3 / 5 : ℝ)
  have hf : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg
    (Real.log_nonneg (one_le_clockScale hM i)) _
  have htop : f j ≤ ∑ i ∈ Finset.range (j + 1), f i :=
    Finset.single_le_sum (fun i hi => hf i) (Finset.mem_range.2 (Nat.lt_succ_self j))
  have hstage : (∑ i ∈ Finset.range j, f (i + 1)) ≤
      ∑ i ∈ Finset.range (j + 1), f i := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (hf 0)
  have hgeom := geometric_log_scale_sum_le_source hM taoAlpha_one_lt
    (by norm_num : (0 : ℝ) < 3 / 5) j hq
  change (∑ i ∈ Finset.range (j + 1), f i) ≤ _ at hgeom
  change 20 * f j + (∑ i ∈ Finset.range j, 40 * f (i + 1)) ≤ _
  rw [← Finset.mul_sum]
  unfold globalClockErrorConstant
  nlinarith

theorem real_clock_source_support_threshold_le {x : ℝ} (hx : 1 ≤ x)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)))
    (q : TaoOddNat)
    (hq : q ∈ (oddLogWindowOddNatPMF (realClockSourceLo x .alpha)
      (realClockSourceHi x .alpha) hmass).support) : x ≤ (q.1 : ℝ) := by
  have hmem : q.1 ∈ oddLogWindow (realClockSourceLo x .alpha)
      (realClockSourceHi x .alpha) := by
    by_contra hn
    exact (PMF.mem_support_iff _ q).mp hq
      (oddLogWindowOddNatPMF_apply_eq_zero_of_not_mem hmass q hn)
  have hlo := (oddLogWindow_mem.mp hmem).1
  have hceil : realClockSourceY x .alpha ≤ (q.1 : ℝ) := Nat.ceil_le.mp hlo
  have hxy : x ≤ realClockSourceY x .alpha :=
    Real.self_le_rpow_of_one_le hx taoAlpha_one_lt.le
  exact hxy.trans hceil

theorem global_clock_good_implies_barrier_clock {M : ℝ} (hM : 1 ≤ M) (j : ℕ)
    (q : TaoOddNat) (hq : q ∈ globalClockGoodEvent M hM j)
    (hsource : clockScale M j ≤ (q.1 : ℝ)) : q ∈ globalBarrierClockEvent M := by
  obtain ⟨τ, hτ, herr, hlanding⟩ := global_clock_good_first_hit hM j q hq
  exact ⟨τ, hτ, herr.trans (global_clock_stage_error_le_source hM j hsource), hlanding⟩

/-- The full finite ladder has an actual successful first passage, centered
at the original source, and an actual final landing above `sqrt M`. -/
theorem global_barrier_clock_failure_probability {M C c : ℝ} (hM : 1 < M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j : ℕ) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      (globalBarrierClockEvent M)ᶜ).toReal ≤ globalClockFailureBudget C c M j := by
  apply le_trans ?_ (global_clock_good_failure_probability hM facts j)
  apply pmf_outer_probability_mono_support
  intro q hq hgood
  exact hq.1 (global_clock_good_implies_barrier_clock hM.le j q hgood
    (real_clock_source_support_threshold_le (one_le_clockScale hM.le j)
      ((facts j).mass_pos .alpha) q hq.2))

end CollatzClockAudit

#print axioms CollatzClockAudit.globalClockErrorConstant_pos
#print axioms CollatzClockAudit.global_clock_stage_error_le_source
#print axioms CollatzClockAudit.real_clock_source_support_threshold_le
#print axioms CollatzClockAudit.global_clock_good_implies_barrier_clock
#print axioms CollatzClockAudit.global_barrier_clock_failure_probability
