import UniformResidualDensityLower
import ForwardOddPrefix
import OccupationLowerValueLimit
import FinitePowerClockGrid
import FixedBasinGreenBoundary

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation.DivergentExcess
open CollatzClockAudit Erdos1135.Tao
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic CollatzCanonical.ForwardComponent

theorem actual_raw_occupation_lower_with_prefix_rate
    {u : ℕ} (hu : Odd u) (hinj : Function.Injective (fun i => iterate i u))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (J : ℕ → ℕ)
    (hJmean : Tendsto (fun R : ℕ => (J R : ℝ) / Real.log (R : ℝ))
      atTop (𝓝 (a / Real.log (3 / 2 : ℝ))))
    (hJbudget : ∀ᶠ R : ℕ in atTop,
      (3 / 2 : ℝ) ^ J R * ((u : ℝ) + 1) ≤ (R : ℝ) + 1)
    (b : ℝ) (hb : b < a / clockDrift + actualFirstHitDensity u *
      ((a / Real.log (3 / 2 : ℝ)) / wholeOrbitCorrection u)) :
    ∀ᶠ R : ℕ in atTop, b ≤ oddTargetDensitySum R / Real.log (R : ℝ) := by
  obtain ⟨theta, htheta, htheta1⟩ := exists_between CollatzCanonical.PackingParameters.beta_lt_one
  obtain ⟨P, C, c, M₀, _, _, hc, _, hfinite⟩ :=
    exists_uniform_finite_occupation_density_lower_with_divergent_future theta htheta htheta1
  obtain ⟨n, hmargin⟩ := exists_finitePowerStep_clock_margin ha ha1
  have hcoeff := (finiteOccupationLower_coefficient_tendsto P theta C c a n htheta1 hc).add_const
    (actualFirstHitDensity u * ((a / Real.log (3 / 2 : ℝ)) / wholeOrbitCorrection u))
  obtain ⟨M, hM, huM, hlarge⟩ := ((eventually_ge_atTop M₀).and
    ((eventually_ge_atTop (u : ℝ)).and (hcoeff.eventually_const_lt hb))).exists
  let B := ⌈M ^ taoAlpha⌉₊
  let f := 1 - 2 * (n + 2 : ℕ) * clockLadderFailureEnvelope C c M * taoAlpha
  have hvalue := ((finiteOccupationLowerValue_div_log_tendsto P theta M a B ha.le).mul_const f).add
    ((hJmean.div_const (wholeOrbitCorrection u)).const_mul (actualFirstHitDensity u))
  have hlarge' : b <
      max 0 (1 - P * M ^ (theta - 1)) * (a / clockDrift) * f +
        actualFirstHitDensity u * ((a / Real.log (3 / 2 : ℝ)) / wholeOrbitCorrection u) := hlarge
  filter_upwards [hvalue.eventually_const_lt hlarge', hJbudget,
    finitePowerClockGrid_eventual_hypotheses ha ha1 n hmargin M B,
    eventually_ge_atTop (2 : ℕ)] with R hvalueR hbudget hgrid hR
  have hR1 : 1 < (R : ℝ) := by exact_mod_cast (show 1 < R by omega)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  obtain ⟨hdown, hbot, htop, hstage, hlast⟩ := hgrid
  have hlower := hfinite M hM (finitePowerClockGrid a n (R : ℝ)) R n u
    (oddForwardPrefix u (J R)) hu huM hinj
    (oddForwardPrefix_mem_properties hu hbudget) hdown hbot htop hstage hlast
  rw [finitePowerClockGrid_zero] at hlower
  have hweights := mul_le_mul_of_nonneg_left (oddForwardPrefix_weight_sum_lower hu hinj (J R))
    (actualFirstHitDensity_nonneg u)
  have hfiniteJ : finiteOccupationLowerValue P theta M R B ((R : ℝ) ^ a) * f +
      actualFirstHitDensity u * ((J R : ℝ) / wholeOrbitCorrection u) ≤ oddTargetDensitySum R := by
    change _ + actualFirstHitDensity u * futureWeightSum u (oddForwardPrefix u (J R)) ≤ _ at hlower
    dsimp only [futureWeightSum] at hlower
    linarith
  have hdiv := div_le_div_of_nonneg_right hfiniteJ hlog.le
  have heq : finiteOccupationLowerValue P theta M R B ((R : ℝ) ^ a) /
      Real.log (R : ℝ) * f + actualFirstHitDensity u *
        (((J R : ℝ) / Real.log (R : ℝ)) / wholeOrbitCorrection u) =
      (finiteOccupationLowerValue P theta M R B ((R : ℝ) ^ a) * f +
        actualFirstHitDensity u * ((J R : ℝ) / wholeOrbitCorrection u)) / Real.log (R : ℝ) := by ring
  rw [heq] at hvalueR
  exact hvalueR.le.trans hdiv

#print axioms actual_raw_occupation_lower_with_prefix_rate

end CollatzCanonical.RawOccupation.DivergentExcess
