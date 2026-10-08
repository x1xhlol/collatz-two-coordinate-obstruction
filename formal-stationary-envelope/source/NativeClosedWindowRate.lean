import NativeWeightedRealRate
import NativeLogWindowCoordinates
import LogarithmicRateComparison

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135.Tao CollatzCylinderPacking.Arithmetic CollatzClockAudit
open CollatzCanonical.DirichletAbelian

/-- A logarithmic power rate for the actual closed harmonic windows at
the native first scale, for every positive or even target alike. -/
theorem native_eventual_closed_window_log_rate :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ c ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ x : ℝ in atTop,
      |closedOddWindowExpectation (firstHitWeight N)
          (taoAlpha ^ 2 * Real.log x) (taoAlpha ^ 3 * Real.log x) -
        closedOddWindowExpectation (firstHitWeight N)
          (taoAlpha * Real.log x) (taoAlpha ^ 2 * Real.log x)| ≤
        C * (Real.log x) ^ (-c) := by
  let b : ℝ := (CollatzCanonical.PackingParameters.beta + 1) / 2
  have hbβ : CollatzCanonical.PackingParameters.beta < b := by
    dsimp [b]; linarith [CollatzCanonical.PackingParameters.beta_lt_one]
  have hb1 : b < 1 := by
    dsimp [b]; linarith [CollatzCanonical.PackingParameters.beta_lt_one]
  obtain ⟨Cpack, Ctv, ctv, hCpack, hCtv, hctv, hcompare⟩ :=
    native_eventual_weighted_real_comparison b hbβ hb1
  let c : ℝ := min ctv 1
  have hc : 0 < c := lt_min hctv zero_lt_one
  refine ⟨2 * Cpack + 400000 + Ctv, c, by positivity, hc, min_le_right _ _, ?_⟩
  intro N
  filter_upwards [hcompare N, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_negative_power_le_log_power (show b - 1 < 0 by linarith) c,
    eventually_negative_power_le_log_power (by norm_num : -(1 / 12800000 : ℝ) < 0) c]
    with x hcompare hx hlog hpack hsmall
  let hmass₁ := hcompare.1 .alpha
  let hmass₂ := hcompare.1 .alphaSq
  have he := hcompare.2 hmass₁ hmass₂
  have he₁ := native_iterated_power_window_expectation (firstHitWeight N)
    (a := taoAlpha) (d := taoAlpha) hx taoAlpha_pos.le hmass₁
  have he₂ := native_iterated_power_window_expectation (firstHitWeight N)
    (a := taoAlpha) (d := taoAlpha ^ 2) hx taoAlpha_sq_pos.le hmass₂
  rw [← pow_two] at he₁
  rw [show taoAlpha * taoAlpha ^ 2 = taoAlpha ^ 3 by ring] at he₂
  dsimp only [realClockSourceLo, realClockSourceHi, realClockSourceY,
    taoSection5BranchExponent] at he
  have hclosed :
      |closedOddWindowExpectation (firstHitWeight N)
          (taoAlpha ^ 2 * Real.log x) (taoAlpha ^ 3 * Real.log x) -
        closedOddWindowExpectation (firstHitWeight N)
          (taoAlpha * Real.log x) (taoAlpha ^ 2 * Real.log x)| ≤
        2 * Cpack * x ^ (b - 1) +
          400000 * x ^ (-(1 / 12800000 : ℝ)) + Ctv * (Real.log x) ^ (-ctv) := by
    rw [← he₁, ← he₂, abs_sub_comm]
    exact he
  have htv := logarithmic_rate_exponent_weaken hlog (min_le_left ctv 1)
  have hp := mul_le_mul_of_nonneg_left hpack (by positivity : 0 ≤ 2 * Cpack)
  have hs := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 400000)
  have ht := mul_le_mul_of_nonneg_left htv hCtv
  nlinarith

#print axioms native_eventual_closed_window_log_rate

end CollatzCanonical.NativeTao
