import SecondScaleFinePrefixExponentialRate
import SecondScaleRealCanonicalClockRates

set_option autoImplicit false
open Filter Topology

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao

theorem half_rpow_le_of_half_le {a b c : ℝ}
    (ha : 0 < a) (hab : a / 2 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    a ^ c / 2 ≤ b ^ c := by
  have hb : 0 < b := by linarith
  have hm : a ^ c ≤ (2 * b) ^ c :=
    Real.rpow_le_rpow ha.le (by linarith) hc
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb.le] at hm
  have ht : (2 : ℝ) ^ c ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc1
  have hmul := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hb.le c)
  linarith

/-- The actual clock event has the stretched exponential failure rate in the
real barrier's logarithm, on both full source windows. -/
theorem eventually_real_local_clock_stretched_exponential :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
          200000 * Real.exp (-(Real.log x) ^ (1 / 5 : ℝ) / 25600) := by
  have hf : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  filter_upwards [eventually_real_clock_bad_probability_sharp,
    eventually_taoProp111RealFloorWindowMassFacts,
    hf.eventually eventually_localPrefixError_stretched_exp,
    eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with x hprob facts hprefix hx hlog
  intro branch hmass
  have hL : 0 < Real.log x := by linarith
  have hhalf := half_log_le_log_floor hx hlog
  have hp := half_rpow_le_of_half_le hL hhalf
    (c := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
  have he : Real.exp (-(Real.log ((Nat.floor x : ℕ) : ℝ)) ^ (1 / 5 : ℝ) / 12800) ≤
      Real.exp (-(Real.log x) ^ (1 / 5 : ℝ) / 25600) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfloor := floorSourceError_le_real_rpow hx
    (show 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) by linarith [facts.log_floor_large])
    (c := 1) (by norm_num) le_rfl
  have hu : (Real.log x) ^ (1 / 5 : ℝ) ≤ Real.log x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ Real.log x by linarith) (show (1 / 5 : ℝ) ≤ 1 by norm_num)
  have hxpow : x ^ (-1 : ℝ) ≤ Real.exp (-(Real.log x) ^ (1 / 5 : ℝ) / 25600) := by
    rw [Real.rpow_def_of_pos (show 0 < x by linarith)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbound := hprob branch hmass
  have hepos := (Real.exp_pos (-(Real.log x) ^ (1 / 5 : ℝ) / 25600)).le
  nlinarith

end CollatzClockSecondScale
