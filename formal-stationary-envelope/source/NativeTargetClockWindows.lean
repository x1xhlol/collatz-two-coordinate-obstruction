import NativeTargetClockEvent
import UniformGlobalBarrierClock

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135.Tao CollatzClockAudit

theorem clockScale_tendsto_atTop {M : ℝ} (hM : 1 < M) :
    Tendsto (clockScale M) atTop atTop := by
  have hp : Tendsto (fun j : ℕ => (taoAlpha : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt taoAlpha_one_lt
  have he := Real.tendsto_exp_atTop.comp
    (Tendsto.const_mul_atTop (Real.log_pos hM) hp)
  apply he.congr'
  exact Eventually.of_forall (fun j => by
    simp only [Function.comp_def, clockScale, Real.rpow_def_of_pos (by linarith : 0 < M)])

/-- The actual target-clock exceptional event has arbitrarily small
probability on all sufficiently high windows of one fixed geometric ladder. -/
theorem actual_target_clock_window_probability (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (d : ℝ) (hd : 0 < d) :
    ∃ M : ℝ, 1 < M ∧ ∀ᶠ j : ℕ in atTop,
      ∃ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha)),
      ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
        (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
        (actualTargetClockBadEvent N ε)).toReal ≤ d := by
  have hlarge : ∀ᶠ M : ℝ in atTop,
      1 < M ∧ (N : ℝ) ≤ M ∧ (N : ℝ) ≤ M ^ (1 / 2 : ℝ) ∧
      (∀ j : ℕ, 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha))) ∧
      ∀ (j : ℕ) (hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha))),
        ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
          (realClockSourceHi (clockScale M j) .alpha) hmass).toOuterMeasure
          (globalBarrierClockEvent M)ᶜ).toReal ≤ d := by
    filter_upwards [eventually_global_barrier_clock_probability hd,
      eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (N : ℝ),
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (N : ℝ)]
      with M hprob hM hN hNsqrt
    exact ⟨by linarith, hN, hNsqrt, hprob.1, hprob.2⟩
  obtain ⟨M, hM, hN, hNsqrt, hmass, hprob⟩ := hlarge.exists
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp
    (eventually_global_barrier_implies_target_clock N hM.le hN hNsqrt hε)
  refine ⟨M, hM, ?_⟩
  filter_upwards [(clockScale_tendsto_atTop hM).eventually_ge_atTop (Q : ℝ)] with j hj
  refine ⟨hmass j, le_trans ?_ (hprob j (hmass j))⟩
  apply pmf_outer_probability_mono_support
  intro q hq hgood
  have hsource := real_clock_source_support_threshold_le (one_le_clockScale hM.le j)
    (hmass j) q hq.2
  have hQq : Q ≤ q.1 := by exact_mod_cast hj.trans hsource
  exact (hQ q.1 hQq q.2 hgood) hq.1

#print axioms clockScale_tendsto_atTop
#print axioms actual_target_clock_window_probability

end CollatzCanonical.NativeTao
