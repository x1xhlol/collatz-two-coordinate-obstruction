import NativeTargetClockWindows
import NativeOddEventDensity

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135.Tao CollatzClockAudit CollatzCanonical.DirichletAbelian

theorem clock_ladder_source_endpoints {M : ℝ} (hM : 0 < M) (j : ℕ) :
    realClockSourceLo (clockScale M j) .alpha =
      ⌈Real.exp (taoAlpha ^ (j + 1) * Real.log M)⌉₊ ∧
    realClockSourceHi (clockScale M j) .alpha =
      ⌊Real.exp (taoAlpha ^ (j + 2) * Real.log M)⌋₊ := by
  have hy : realClockSourceY (clockScale M j) .alpha = clockScale M (j + 1) := by
    exact (clockScale_succ hM.le j).symm
  constructor
  · rw [realClockSourceLo, hy, taoNyLo, clockScale, Real.rpow_def_of_pos hM, mul_comm]
  · rw [realClockSourceHi, hy, taoNyHi, ← clockScale_succ hM.le (j + 1)]
    rw [clockScale, Real.rpow_def_of_pos hM, mul_comm]

theorem native_odd_probability_congr (G : Set TaoOddNat) {lo hi lo' hi' : ℕ}
    (hl : lo = lo') (hu : hi = hi')
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hmass' : 0 < logFinsetMass (oddLogWindow lo' hi')) :
    ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure G).toReal =
      ((oddLogWindowOddNatPMF lo' hi' hmass').toOuterMeasure G).toReal := by
  subst lo'
  subst hi'
  rfl

theorem actual_target_clock_ladder_window_probability (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (d : ℝ) (hd : 0 < d) :
    ∃ M : ℝ, 1 < M ∧ ∀ᶠ j : ℕ in atTop,
      ∃ hmass : 0 < logFinsetMass (oddLogWindow
        ⌈Real.exp (taoAlpha ^ (j + 1) * Real.log M)⌉₊
        ⌊Real.exp (taoAlpha ^ (j + 2) * Real.log M)⌋₊),
      ((oddLogWindowOddNatPMF
        ⌈Real.exp (taoAlpha ^ (j + 1) * Real.log M)⌉₊
        ⌊Real.exp (taoAlpha ^ (j + 2) * Real.log M)⌋₊ hmass).toOuterMeasure
        (actualTargetClockBadEvent N ε)).toReal ≤ d := by
  obtain ⟨M, hM, hprob⟩ := actual_target_clock_window_probability N hε d hd
  refine ⟨M, hM, ?_⟩
  filter_upwards [hprob] with j hj
  obtain ⟨hmass, hp⟩ := hj
  obtain ⟨hl, hu⟩ := clock_ladder_source_endpoints (by linarith : 0 < M) j
  have hmass' : 0 < logFinsetMass (oddLogWindow
      ⌈Real.exp (taoAlpha ^ (j + 1) * Real.log M)⌉₊
      ⌊Real.exp (taoAlpha ^ (j + 2) * Real.log M)⌋₊) := by
    rw [← hl, ← hu]
    exact hmass
  refine ⟨hmass', ?_⟩
  rw [← native_odd_probability_congr (actualTargetClockBadEvent N ε) hl hu hmass hmass']
  exact hp

/-- The actual target odd-clock exceptional set has absolute odd
logarithmic density zero for every target, including even targets. -/
theorem actual_target_clock_exception_logarithmic_mean_zero (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun t : ℝ =>
      oddLogarithmicCumulative (oddEventWeight (actualTargetClockBadEvent N ε)) t / t)
      atTop (𝓝 0) :=
  native_odd_event_logarithmic_mean_zero (actualTargetClockBadEvent N ε) taoAlpha_one_lt
    (actual_target_clock_ladder_window_probability N hε)

#print axioms actual_target_clock_ladder_window_probability
#print axioms actual_target_clock_exception_logarithmic_mean_zero

end CollatzCanonical.NativeTao
