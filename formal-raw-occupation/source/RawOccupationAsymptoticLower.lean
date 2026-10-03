import OccupationLowerValueLimit
import FinitePowerClockGrid

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open CollatzClockAudit Erdos1135.Tao

/-- The actual raw first-hit density trace has the sharp descent-clock
lower bound. This asserts lower comparisons and allows unbounded growth. -/
theorem actual_raw_occupation_eventual_lower (b : ℝ) (hb : b < 1 / clockDrift) :
    ∀ᶠ R : ℕ in atTop, b ≤ oddTargetDensitySum R / Real.log (R : ℝ) := by
  obtain ⟨theta, htheta, htheta1⟩ := exists_between CollatzCanonical.PackingParameters.beta_lt_one
  obtain ⟨P, C, c, M₀, hP, hC, hc, hM₀, hfinite⟩ :=
    exists_uniform_finite_occupation_density_lower theta htheta htheta1
  have hbmul : b * clockDrift < 1 := (lt_div_iff₀ clockDrift_pos).mp hb
  obtain ⟨a, ha, ha1⟩ := exists_between
    (show max 0 (b * clockDrift) < 1 from max_lt_iff.mpr ⟨by norm_num, hbmul⟩)
  have ha0 : 0 < a := (le_max_left _ _).trans_lt ha
  have hba : b < a / clockDrift :=
    (lt_div_iff₀ clockDrift_pos).mpr ((le_max_right _ _).trans_lt ha)
  obtain ⟨n, hmargin⟩ := exists_finitePowerStep_clock_margin ha0 ha1
  have hcoeff := finiteOccupationLower_coefficient_tendsto P theta C c a n htheta1 hc
  obtain ⟨M, hM, hlarge⟩ := ((eventually_ge_atTop M₀).and
    (hcoeff.eventually_const_lt hba)).exists
  let B := ⌈M ^ taoAlpha⌉₊
  let f := 1 - 2 * (n + 2 : ℕ) * clockLadderFailureEnvelope C c M * taoAlpha
  have hvalue := (finiteOccupationLowerValue_div_log_tendsto P theta M a B ha0.le).mul_const f
  have hlarge' : b < max 0 (1 - P * M ^ (theta - 1)) * (a / clockDrift) * f := hlarge
  filter_upwards [hvalue.eventually_const_lt hlarge',
    finitePowerClockGrid_eventual_hypotheses ha0 ha1 n hmargin M B,
    eventually_ge_atTop (2 : ℕ)] with R hvalueR hgrid hR
  have hR1 : 1 < (R : ℝ) := by exact_mod_cast (show 1 < R by omega)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  obtain ⟨hdown, hbot, htop, hstage, hlast⟩ := hgrid
  have hlower := hfinite M hM (finitePowerClockGrid a n (R : ℝ)) R n
    hdown hbot htop hstage hlast
  rw [finitePowerClockGrid_zero] at hlower
  have hdiv := div_le_div_of_nonneg_right hlower hlog.le
  have heq : finiteOccupationLowerValue P theta M R B ((R : ℝ) ^ a) /
      Real.log (R : ℝ) * f =
      (finiteOccupationLowerValue P theta M R B ((R : ℝ) ^ a) * f) /
        Real.log (R : ℝ) := by ring
  rw [heq] at hvalueR
  exact hvalueR.le.trans hdiv

#print axioms actual_raw_occupation_eventual_lower

end CollatzCanonical.RawOccupation
