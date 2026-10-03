import ClosedWindowCumulativeAdapter
import UniformGlobalBarrierClock
import NativeTargetClockDensity

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit
open CollatzCanonical.DirichletAbelian CollatzCanonical.NativeTao

/-- A fixed event retaining every lower-stage clock at some sufficiently high rung. -/
def fixedLadderGoodEvent (M : ℝ) (hM : 1 ≤ M) (n : ℕ) : Set TaoOddNat :=
  {q | ∃ j, n ≤ j ∧ q ∈ globalClockGoodEvent M hM j}

theorem fixedLadderGoodEvent_failure_subset {M : ℝ} (hM : 1 ≤ M)
    {n j : ℕ} (hnj : n ≤ j) :
    (fixedLadderGoodEvent M hM n)ᶜ ⊆ (globalClockGoodEvent M hM j)ᶜ := by
  intro q hq hgood
  exact hq ⟨j, hnj, hgood⟩

theorem fixedLadderGoodEvent_failure_probability {M C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i))
    {n j : ℕ} (hnj : n ≤ j) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      (fixedLadderGoodEvent M hM.le n)ᶜ).toReal ≤ clockLadderFailureEnvelope C c M := by
  apply le_trans (pmf_outer_probability_mono_support _
    (fun q hq => fixedLadderGoodEvent_failure_subset hM.le hnj hq.1))
  apply (global_clock_good_failure_probability hM facts j).trans
  rw [globalClockFailureBudget_eq_clockLadderFailureBudget]
  exact clockLadderFailureBudget_le_envelope hC hc hMe j

theorem fixedLadderGoodEvent_closed_window_bound {M C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i))
    {n j : ℕ} (hnj : n ≤ j) :
    closedOddWindowExpectation (oddEventWeight (fixedLadderGoodEvent M hM.le n)ᶜ)
      (taoAlpha ^ (j + 1) * Real.log M) (taoAlpha ^ (j + 2) * Real.log M) ≤
        clockLadderFailureEnvelope C c M := by
  have hp := fixedLadderGoodEvent_failure_probability hC hc hM hMe facts hnj
  obtain ⟨hl, hu⟩ := clock_ladder_source_endpoints (by linarith : 0 < M) j
  have hmass : 0 < logFinsetMass (oddLogWindow
      ⌈Real.exp (taoAlpha ^ (j + 1) * Real.log M)⌉₊
      ⌊Real.exp (taoAlpha ^ (j + 2) * Real.log M)⌋₊) := by
    rw [← hl, ← hu]
    exact (facts j).mass_pos .alpha
  rw [native_odd_probability_congr _ hl hu ((facts j).mass_pos .alpha) hmass] at hp
  have hs : 0 ≤ taoAlpha ^ (j + 1) * Real.log M :=
    mul_nonneg (pow_nonneg taoAlpha_pos.le _) (Real.log_pos hM).le
  rwa [native_odd_event_eq_closed_expectation _ hs hmass] at hp

theorem fixedLadderGoodEvent_failure_cumulative_envelope {M C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (n : ℕ) :
    ∃ A : ℝ, ∀ᶠ t : ℝ in atTop,
      oddLogarithmicCumulative (oddEventWeight (fixedLadderGoodEvent M hM.le n)ᶜ) t ≤
        A + clockLadderFailureEnvelope C c M * taoAlpha * t := by
  have hE : 0 ≤ clockLadderFailureEnvelope C c M :=
    ENNReal.toReal_nonneg.trans
      (fixedLadderGoodEvent_failure_probability hC hc hM hMe facts (le_refl n))
  apply odd_cumulative_envelope_of_ladder_windows
    (fun q => (oddEventWeight_bounds _ q).1)
    (fun q => (oddEventWeight_bounds _ q).2) taoAlpha_one_lt hM hE
  filter_upwards [eventually_ge_atTop n] with j hj
  exact fixedLadderGoodEvent_closed_window_bound hC hc hM hMe facts hj

theorem fixedLadderGoodEvent_failure_normalized_cumulative {M C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      2 * oddLogarithmicCumulative (oddEventWeight (fixedLadderGoodEvent M hM.le n)ᶜ) t / t ≤
        2 * clockLadderFailureEnvelope C c M * taoAlpha + ε := by
  have hE : 0 ≤ clockLadderFailureEnvelope C c M :=
    ENNReal.toReal_nonneg.trans
      (fixedLadderGoodEvent_failure_probability hC hc hM hMe facts (le_refl n))
  apply odd_normalized_cumulative_eventual_le_of_ladder_windows
    (fun q => (oddEventWeight_bounds _ q).1)
    (fun q => (oddEventWeight_bounds _ q).2) taoAlpha_one_lt hM hE _ hε
  filter_upwards [eventually_ge_atTop n] with j hj
  exact fixedLadderGoodEvent_closed_window_bound hC hc hM hMe facts hj

#print axioms fixedLadderGoodEvent_failure_subset
#print axioms fixedLadderGoodEvent_failure_probability
#print axioms fixedLadderGoodEvent_closed_window_bound
#print axioms fixedLadderGoodEvent_failure_cumulative_envelope
#print axioms fixedLadderGoodEvent_failure_normalized_cumulative

end CollatzCanonical.RawOccupation
