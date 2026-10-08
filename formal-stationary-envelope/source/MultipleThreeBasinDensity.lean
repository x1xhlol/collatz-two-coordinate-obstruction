import BasinMapBridges
import BasinWeightedDensityComparison
import LogarithmicFinitePerturbation

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze
open CollatzCylinderPacking

namespace CollatzCylinderPacking.Arithmetic

theorem odd_basin_multiple_three_eq_zero {N q : ℕ} (hN : N % 3 = 0)
    (ho : q % 2 = 1) (hne : q ≠ N) : basinIndicator N q = 0 := by
  classical
  have hno : ¬ ∃ k, iterate k q = N := by
    rintro ⟨k, hk⟩
    have he := (CollatzBasinMapBridges.hit_multiple_of_three_iff k q N hN).mp hk
    cases k with
    | zero => simp only [pow_zero, one_mul] at he; exact hne he
    | succ k =>
      rw [pow_succ] at he
      have he' : q = 2 * (2 ^ k * N) := he.trans (by ring)
      omega
  simp only [basinIndicator, if_neg hno]

theorem actual_basin_density_zero_of_multiple_three {N : ℕ} (hN : N % 3 = 0) :
    actualBasinDensity N = 0 := by
  have hzero : Tendsto (fun t : ℝ => logarithmicCumulative (oddBasinIndicator N) t / t)
      atTop (𝓝 0) := by
    apply zero_logarithmic_mean_of_eventual_le (v := fun _ => 0)
    · intro q
      unfold oddBasinIndicator
      split_ifs
      · exact basinIndicator_bounds N q
      · norm_num
    · intro q; rfl
    · filter_upwards [eventually_gt_atTop N] with q hq
      unfold oddBasinIndicator
      split_ifs with ho
      · rw [odd_basin_multiple_three_eq_zero hN ho (by omega)]
      · rfl
    · simpa only [logarithmicCumulative, zero_div, Finset.sum_const_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  have h := tendsto_nhds_unique (actual_basin_odd_mean N) hzero
  linarith

theorem actual_weighted_density_zero_of_multiple_three {N : ℕ} (hN : N % 3 = 0) :
    actualFirstHitDensity N = 0 := by
  obtain ⟨P, hP, hcompare⟩ := actual_basin_and_weighted_density_comparison
  have h := hcompare N
  rw [actual_basin_density_zero_of_multiple_three hN] at h
  nlinarith

theorem actual_trace_zero_of_multiple_three {N : ℕ} (hN : N % 3 = 0) :
    actualDensityValue actualFirstHitDensity N = 0 := by
  simp only [actualDensityValue, actual_weighted_density_zero_of_multiple_three hN, mul_zero]

#print axioms actual_basin_density_zero_of_multiple_three
#print axioms actual_weighted_density_zero_of_multiple_three
#print axioms actual_trace_zero_of_multiple_three

end CollatzCylinderPacking.Arithmetic
