import FiniteCylinderMaximum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCylinderPacking.Arithmetic

theorem maximum_residue_log_bounds {k : ℕ} (hk : 0 < k) :
    Real.log 2 - Real.log (2 * (k : ℝ) + 3) / (k : ℝ) ≤
        -Real.log (maximumResidueMass k) / (k : ℝ) ∧
      -Real.log (maximumResidueMass k) / (k : ℝ) ≤ Real.log 2 := by
  have hb := maximum_residue_mass_bounds hk
  have hp : 0 < maximumResidueMass k := lt_of_lt_of_le (by positivity) hb.1
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlo := Real.log_le_log (by positivity : 0 < (1 / 2 : ℝ) ^ k) hb.1
  have hhi := Real.log_le_log hp hb.2
  have he1 : Real.log ((1 / 2 : ℝ) ^ k) = -(k : ℝ) * Real.log 2 := by
    rw [Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have he2 : Real.log ((2 * (k : ℝ) + 3) / (2 : ℝ) ^ k) =
      Real.log (2 * (k : ℝ) + 3) - (k : ℝ) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [he1] at hlo
  rw [he2] at hhi
  constructor
  · apply (le_div_iff₀ hkR).mpr
    have he : (Real.log 2 - Real.log (2 * (k : ℝ) + 3) / (k : ℝ)) * (k : ℝ) =
        (k : ℝ) * Real.log 2 - Real.log (2 * (k : ℝ) + 3) := by
      field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hkR).mpr
    linarith

theorem polynomial_log_over_depth_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log (2 * (k : ℝ) + 3) / (k : ℝ)) atTop (𝓝 0) := by
  have hc : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun k : ℕ => 2 * (k : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 (hc.const_mul_atTop (by norm_num))
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-(3 / 2)) 1 (by norm_num)).comp hx
  convert ht using 1
  funext k
  congr 1
  · simp
  · ring

theorem maximum_residue_exponential_rate :
    Tendsto (fun k : ℕ => -Real.log (maximumResidueMass k) / (k : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have hlo : Tendsto (fun k : ℕ => Real.log 2 - Real.log (2 * (k : ℝ) + 3) / (k : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub polynomial_log_over_depth_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact (maximum_residue_log_bounds hk).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact (maximum_residue_log_bounds hk).2

theorem maximum_residue_base_three_rate :
    Tendsto (fun k : ℕ => -Real.log (maximumResidueMass k) / ((k : ℝ) * Real.log 3))
      atTop (𝓝 (Real.log 2 / Real.log 3)) := by
  have h := maximum_residue_exponential_rate.div_const (Real.log 3)
  simpa only [div_div] using h

#print axioms maximum_residue_log_bounds
#print axioms maximum_residue_exponential_rate
#print axioms maximum_residue_base_three_rate

end CollatzCylinderPacking.Arithmetic
