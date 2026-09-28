import NativeBasinFirstScaleWindowRate
import NativeBasinSecondScaleWindowRate

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.DirichletAbelian

open CollatzCylinderPacking.Arithmetic

/-- The actual basin indicator has an odd logarithmic mean for every
target. Both quantitative window inputs are discharged by the checked
native Tao and large-landing estimates at the two distinct scales. -/
theorem actual_basin_odd_logarithmic_mean_exists (N : ℕ) :
    ∃ D : ℝ, Tendsto
      (fun t => oddLogarithmicCumulative (basinIndicator N) t / t) atTop (𝓝 D) := by
  obtain ⟨C, c, hC, hc, hc1, hfirst⟩ :=
    CollatzCanonical.NativeTao.native_basin_first_scale_normalized_window_rate
  obtain ⟨E, e, _, he, _, hsecond⟩ :=
    CollatzCanonical.NativeTao.native_basin_second_scale_normalized_window_rate
  have hα : Erdos1135.Tao.taoAlpha = (1001 / 1000 : ℝ) := by
    norm_num [Erdos1135.Tao.taoAlpha]
  have hβ : Erdos1135SecondScale.Tao.taoAlpha = (2001 / 2000 : ℝ) := by
    norm_num [Erdos1135SecondScale.Tao.taoAlpha]
  have hirr : Irrational
      (Real.log Erdos1135.Tao.taoAlpha / Real.log Erdos1135SecondScale.Tao.taoAlpha) := by
    rw [hα, hβ]
    exact CollatzCanonical.Scales.logarithms_incommensurable
  exact odd_weighted_mean_of_two_eventual_closed_rates (basinIndicator N)
    (fun q => (basinIndicator_bounds N q).1) (fun q => (basinIndicator_bounds N q).2)
    Erdos1135.Tao.taoAlpha_one_lt Erdos1135SecondScale.Tao.taoAlpha_one_lt
    hC hc hc1 he hirr (hfirst N) (hsecond N)

#print axioms actual_basin_odd_logarithmic_mean_exists

end CollatzCanonical.DirichletAbelian
