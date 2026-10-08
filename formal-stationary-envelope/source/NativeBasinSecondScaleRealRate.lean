import NativeBasinPassageComparison
import SecondScaleRealCanonicalClockRates

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135SecondScale.Tao CollatzCylinderPacking.Arithmetic CollatzClockSecondScale

/-- The checked real landing estimate and checked real passage-law estimate
give the quantitative basin comparison for both actual Tao source windows. -/
theorem native_second_scale_eventual_basin_real_comparison (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ Cpack Ctv ctv : ℝ, 0 ≤ Cpack ∧ 0 ≤ Ctv ∧ 0 < ctv ∧
      ∀ N : ℕ, ∀ᶠ x : ℝ in atTop,
        (∀ branch : TaoSection5SourceBranch, 0 < logFinsetMass
          (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) ∧
        ∀ (hmass₁ : 0 < logFinsetMass
            (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)))
          (hmass₂ : 0 < logFinsetMass
            (oddLogWindow (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq))),
          |pmfExpectation
              (oddLogWindowPMF (realClockSourceLo x .alpha) (realClockSourceHi x .alpha) hmass₁)
              (fun q => basinIndicator N q.1) -
            pmfExpectation
              (oddLogWindowPMF (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) hmass₂)
              (fun q => basinIndicator N q.1)| ≤
            2 * Cpack * x ^ (b - 1) +
              400000 * x ^ (-(1 / 12800000 : ℝ)) + Ctv * (Real.log x) ^ (-ctv) := by
  obtain ⟨Cpack, hCpack, hcompare⟩ := native_real_windows_basin_comparison b hbβ hb1
  obtain ⟨errNoHit, errTV, Ctv, ctv, hCtv, hctv, hrates, hTV⟩ :=
    taoProp111RealFirstPassageStabilizationRate_checked
  refine ⟨Cpack, Ctv, ctv, hCpack, hCtv, hctv, ?_⟩
  intro N
  filter_upwards [eventually_real_local_clock_and_landing_rates, hrates,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (N : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (N : ℝ)]
    with x hlanding hrates hx hN hNsqrt
  refine ⟨hlanding.1, ?_⟩
  intro hmass₁ hmass₂
  have hG : ∀ q ∈ realLargeLandingGoodEvent x,
      ∃ n, syracuseFirstHitAtMostReal x q.1 n ∧ N < (syracuse^[n]) q.1 := by
    intro q hq
    obtain ⟨n, hfirst, hlarge⟩ := hq
    exact ⟨n, hfirst, by exact_mod_cast lt_of_le_of_lt hNsqrt hlarge⟩
  have hbound := hcompare N x hx hN (realLargeLandingGoodEvent x) hG
    (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)
    (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) hmass₁ hmass₂
  change
    |pmfExpectation
        (oddLogWindowPMF (realClockSourceLo x .alpha) (realClockSourceHi x .alpha) hmass₁)
        (fun q => basinIndicator N q.1) -
      pmfExpectation
        (oddLogWindowPMF (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) hmass₂)
        (fun q => basinIndicator N q.1)| ≤
      2 * Cpack * x ^ (b - 1) +
      ((oddLogWindowOddNatPMF (realClockSourceLo x .alpha)
        (realClockSourceHi x .alpha) hmass₁).toOuterMeasure
          (realLargeLandingGoodEvent x)ᶜ).toReal +
      ((oddLogWindowOddNatPMF (realClockSourceLo x .alphaSq)
        (realClockSourceHi x .alphaSq) hmass₂).toOuterMeasure
          (realLargeLandingGoodEvent x)ᶜ).toReal +
      syracusePassRealFloorWindowTV x (realClockSourceLo x .alpha)
        (realClockSourceHi x .alpha) (realClockSourceLo x .alphaSq)
        (realClockSourceHi x .alphaSq) hx hmass₁ hmass₂ at hbound
  have hp₁ := (hlanding.2 .alpha hmass₁).2
  have hp₂ := (hlanding.2 .alphaSq hmass₂).2
  have hpair : TaoProp111RealWindowPair x
      (realClockSourceLo x .alpha) (realClockSourceHi x .alpha)
      (realClockSourceLo x .alphaSq) (realClockSourceHi x .alphaSq) := ⟨rfl, rfl, rfl, rfl⟩
  have htv := (hTV x _ _ _ _ hx hpair hmass₁ hmass₂).2.2
  have htvRate := hrates.2.2.2
  linarith

#print axioms native_second_scale_eventual_basin_real_comparison

end CollatzCanonical.NativeTao
