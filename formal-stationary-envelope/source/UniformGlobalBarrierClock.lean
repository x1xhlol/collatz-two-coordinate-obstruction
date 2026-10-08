import GlobalBarrierClock
import ClockLadderFailureBudget

open Filter
open scoped Topology

namespace CollatzClockAudit
open Erdos1135.Tao

theorem globalClockFailureBudget_eq_clockLadderFailureBudget (C c M : ℝ) (j : ℕ) :
    globalClockFailureBudget C c M j = clockLadderFailureBudget C c M j := by
  simp only [globalClockFailureBudget, clockLadderFailureBudget, add_assoc]

theorem global_barrier_clock_failure_le_envelope {M C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : Real.exp 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j : ℕ)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha))) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
      (globalBarrierClockEvent M)ᶜ).toReal ≤ clockLadderFailureEnvelope C c M := by
  have hM1 : 1 < M := (Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 1)).trans_le hM
  apply (global_barrier_clock_failure_probability hM1 facts j).trans
  rw [globalClockFailureBudget_eq_clockLadderFailureBudget]
  exact clockLadderFailureBudget_le_envelope hC hc hM j

/-- A single envelope tending to zero controls the actual centered barrier
clock and the actual final large landing, uniformly in every ladder height. -/
theorem exists_eventually_global_barrier_clock_envelope :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      Tendsto (clockLadderFailureEnvelope C c) atTop (𝓝 0) ∧
      ∀ᶠ M : ℝ in atTop, (∀ j : ℕ, 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha))) ∧
        ∀ (j : ℕ) (hmass : 0 < logFinsetMass
          (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
            (realClockSourceHi (clockScale M j) .alpha))),
          ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
            (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
            (globalBarrierClockEvent M)ᶜ).toReal ≤ clockLadderFailureEnvelope C c M := by
  obtain ⟨C, c, M₀, hC, hc, _, hfacts⟩ := exists_clock_scale_uniform_cutoff
  refine ⟨C, c, hC, hc, clockLadderFailureEnvelope_tendsto_zero hc, ?_⟩
  filter_upwards [eventually_ge_atTop M₀, eventually_ge_atTop (Real.exp 1)] with M hM hMe
  have facts := hfacts M hM
  exact ⟨fun j => (facts j).mass_pos .alpha,
    fun j hm => global_barrier_clock_failure_le_envelope hC hc hMe facts j hm⟩

/-- Unconditional global barrier clock law in each full geometric source
window. Nontermination is included in the exceptional event. -/
theorem eventually_global_barrier_clock_probability {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℝ in atTop, (∀ j : ℕ, 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha))) ∧
      ∀ (j : ℕ) (hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha))),
        ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
          (globalBarrierClockEvent M)ᶜ).toReal ≤ ε := by
  obtain ⟨C, c, _, _, htend, hfacts⟩ := exists_eventually_global_barrier_clock_envelope
  filter_upwards [hfacts, htend.eventually_le_const hε] with M hM hbound
  exact ⟨hM.1, fun j hm => (hM.2 j hm).trans hbound⟩

end CollatzClockAudit

#print axioms CollatzClockAudit.globalClockFailureBudget_eq_clockLadderFailureBudget
#print axioms CollatzClockAudit.global_barrier_clock_failure_le_envelope
#print axioms CollatzClockAudit.exists_eventually_global_barrier_clock_envelope
#print axioms CollatzClockAudit.eventually_global_barrier_clock_probability
