import ActualBasinOddMeanExistence
import BasinIndicatorFullMean

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian

namespace CollatzCylinderPacking.Arithmetic

/-- The logarithmic density of the ordinary, unweighted target basin. -/
noncomputable def actualBasinDensity (N : ℕ) : ℝ :=
  2 * Classical.choose (actual_basin_odd_logarithmic_mean_exists N)

theorem actual_basin_odd_mean (N : ℕ) :
    Tendsto (fun t : ℝ => logarithmicCumulative (oddBasinIndicator N) t / t)
      atTop (𝓝 (actualBasinDensity N / 2)) := by
  have h := Classical.choose_spec (actual_basin_odd_logarithmic_mean_exists N)
  convert h using 1
  congr 1
  unfold actualBasinDensity
  ring

/-- Every fixed Collatz basin has an unweighted logarithmic density. Both
scale estimates and the initial even-step correction are discharged. -/
theorem actual_basin_full_logarithmic_mean (N : ℕ) :
    Tendsto (fun t : ℝ => logarithmicCumulative (basinIndicator N) t / t)
      atTop (𝓝 (actualBasinDensity N)) := by
  convert basin_full_mean_of_odd_mean N (actual_basin_odd_mean N) using 1
  congr 1
  ring

theorem actualBasinDensity_bounds (N : ℕ) :
    0 ≤ actualBasinDensity N ∧ actualBasinDensity N ≤ 1 := by
  have hmean := actual_basin_full_logarithmic_mean N
  have hnonneg : ∀ᶠ t : ℝ in atTop,
      0 ≤ logarithmicCumulative (basinIndicator N) t / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_nonneg (logarithmicCumulative_nonneg
      (fun q => (basinIndicator_bounds N q).1) t) ht.le
  have hupper : ∀ᶠ t : ℝ in atTop,
      logarithmicCumulative (basinIndicator N) t / t ≤ 1 + 1 / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hb := logarithmicCumulative_linear_bound
      (fun q => (basinIndicator_bounds N q).1) (fun q => (basinIndicator_bounds N q).2) ht.le
    have ha := le_abs_self (logarithmicCumulative (basinIndicator N) t)
    apply (div_le_iff₀ ht).mpr
    have hid : (1 + 1 / t) * t = t + 1 := by field_simp
    rw [hid]
    linarith
  have hlim : Tendsto (fun t : ℝ => 1 + 1 / t) atTop (𝓝 1) := by
    simpa only [one_div, add_zero] using tendsto_inv_atTop_zero.const_add (1 : ℝ)
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hmean hnonneg,
    le_of_tendsto_of_tendsto hmean hlim hupper⟩

/-- The usual reciprocal sum on integer cutoffs has the same density. -/
theorem actual_basin_reciprocal_density (N : ℕ) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.range X, basinIndicator N (n + 1) / (n + 1 : ℕ)) /
        Real.log (X : ℝ)) atTop (𝓝 (actualBasinDensity N)) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply ((actual_basin_full_logarithmic_mean N).comp hlog).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  simp only [Function.comp_def, logarithmicCumulative, Real.exp_log hx, Nat.floor_natCast]

end CollatzCylinderPacking.Arithmetic
