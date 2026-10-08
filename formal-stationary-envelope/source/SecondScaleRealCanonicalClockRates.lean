import SecondScaleRealLocalClockProbability
import SecondScaleRealClockRateBounds

open Filter
open scoped Topology

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao

theorem eventually_real_local_clock_log_power :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
          200000 * (Real.log x) ^ (-(1 / 10 : ℝ)) := by
  filter_upwards [eventually_real_clock_bad_probability_floor_log_power,
    eventually_taoProp111RealFloorWindowMassFacts, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hprob facts hx hlog
  intro branch hmass
  have hf := floor_log_rpow_neg_le_two_mul hx hlog
    (c := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
  have he := floorSourceError_le_real_log_rpow hx
    (show 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) by linarith [facts.log_floor_large])
    (show 1 ≤ Real.log x by linarith) (c := (1 / 10 : ℝ)) (by norm_num)
  have hp := hprob branch hmass
  have hn : 0 ≤ (Real.log x) ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith

theorem eventually_real_large_landing_polynomial :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure (realLargeLandingGoodEvent x)ᶜ).toReal ≤
          200000 * x ^ (-(1 / 12800000 : ℝ)) := by
  filter_upwards [eventually_real_landing_bad_probability_floor_power,
    eventually_taoProp111RealFloorWindowMassFacts, eventually_ge_atTop (2 : ℝ)] with x hprob facts hx
  intro branch hmass
  have hf := floor_rpow_neg_le_two_mul hx
    (c := (1 / 12800000 : ℝ)) (by norm_num) (by norm_num)
  have he := floorSourceError_le_real_rpow hx
    (show 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) by linarith [facts.log_floor_large])
    (c := (1 / 12800000 : ℝ)) (by norm_num) (by norm_num)
  have hp := hprob branch hmass
  have hn : 0 ≤ x ^ (-(1 / 12800000 : ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- Both actual real source windows are nonempty, and both quantitative
local laws hold with their displayed real-threshold rates. -/
theorem eventually_real_local_clock_and_landing_rates :
    ∀ᶠ x : ℝ in atTop,
      (∀ branch : TaoSection5SourceBranch, 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) ∧
      ∀ (branch : TaoSection5SourceBranch)
        (hmass : 0 < logFinsetMass
          (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))),
        ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
          hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
            200000 * (Real.log x) ^ (-(1 / 10 : ℝ)) ∧
        ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
          hmass).toOuterMeasure (realLargeLandingGoodEvent x)ᶜ).toReal ≤
            200000 * x ^ (-(1 / 12800000 : ℝ)) := by
  filter_upwards [eventually_taoProp111RealFloorWindowMassFacts,
    eventually_real_local_clock_log_power, eventually_real_large_landing_polynomial]
    with x facts hclock hlanding
  exact ⟨real_clock_source_mass_pos facts,
    fun branch hmass => ⟨hclock branch hmass, hlanding branch hmass⟩⟩

end CollatzClockSecondScale

#print axioms CollatzClockSecondScale.eventually_real_local_clock_log_power
#print axioms CollatzClockSecondScale.eventually_real_large_landing_polynomial
#print axioms CollatzClockSecondScale.eventually_real_local_clock_and_landing_rates
