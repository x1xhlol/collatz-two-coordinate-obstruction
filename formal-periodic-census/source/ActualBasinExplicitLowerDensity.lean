import BoundedPredecessorDensity
import BasinPositiveNaturalCriterion
import CollatzPredecessorDensity

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open CollatzCylinderPacking.Arithmetic CollatzBasinMapBridges

theorem actual_basin_density_ge_explicit_floor {N : ℕ}
    (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    predecessorDensityFloor (2 * N) ≤ actualBasinDensity N := by
  have hdouble : ¬ 3 ∣ 2 * N := by omega
  obtain ⟨X0, hcount⟩ := generalTarget_predecessors_explicit_lower_density
    (a := 2 * N) (by omega) hdouble
  have hS : ∀ q ∈ CollatzPredecessorDensity.predecessors (2 * N),
      0 < q ∧ basinIndicator N q = 1 := by
    intro q hq
    exact ⟨hq.1, native_predecessor_double_basin hq.2⟩
  exact basin_density_ge_positive_count_rate _ N (predecessorDensityFloor (2 * N)) X0 hS hcount

theorem actual_basin_density_ge_explicit_exponential {N : ℕ}
    (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    Real.exp (-Real.log 3 *
      (88 * (Erdos1135Predecessor.ND.PositiveDensity.explicitSyracuseMixingCoefficient : ℝ) *
        ((predecessorSeedMultiplier * (2 * N) : ℕ) : ℝ)) ^ (1 / 6 : ℝ)) /
      (256 * ((predecessorSeedMultiplier * (2 * N) : ℕ) : ℝ)) ≤ actualBasinDensity N :=
  (predecessorDensityFloor_ge_exp (by omega : 0 < 2 * N)).trans
    (actual_basin_density_ge_explicit_floor hN hunit)

#print axioms actual_basin_density_ge_explicit_floor
#print axioms actual_basin_density_ge_explicit_exponential

end CollatzCanonical.BoundedInverseSeed
