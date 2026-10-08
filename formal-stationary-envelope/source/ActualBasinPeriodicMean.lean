import BasinAdjacentVariation
import PeriodicSourceMean
import NaturalScalarPrefix
import OddTerminalFanMean

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking.Arithmetic CollatzCanonical.NativeTao

theorem basinIndicator_abs_le_one (N q : ℕ) : |basinIndicator N q| ≤ 1 := by
  rw [abs_of_nonneg (basinIndicator_bounds N q).1]
  exact (basinIndicator_bounds N q).2

theorem actual_basin_sourceMean (N : ℕ) :
    Tendsto (sourceMean (basinIndicator N)) atTop (𝓝 (actualBasinDensity N)) :=
  sourceMean_of_shift (basinIndicator N) (basinIndicator_abs_le_one N)
    (actual_basin_natural_density N)

theorem actual_basin_adjacentVariation (N : ℕ) :
    Tendsto (fun X => adjacentVariation (basinIndicator N) X / (X : ℝ))
      atTop (𝓝 0) :=
  CollatzCanonical.GaoShortcut.basin_adjacent_variation_tendsto_zero N

theorem actual_basin_periodic_sourceMean (N : ℕ) (p : ℕ → ℝ) (M : ℕ)
    (hM : 0 < M) (hp : Function.Periodic p M) :
    Tendsto (sourceMean (fun q => basinIndicator N q * p q)) atTop
      (𝓝 (actualBasinDensity N * ((∑ q ∈ Finset.range M, p q) / (M : ℝ)))) :=
  periodic_weighted_mean (basinIndicator N) p M hM hp
    (basinIndicator_abs_le_one N) (actual_basin_adjacentVariation N)
    (actual_basin_sourceMean N)

theorem actual_basin_oddTerminalFan_sourceMean (N m : ℕ) :
    Tendsto (sourceMean (fun q => basinIndicator N q * oddTerminalFan m q))
      atTop (𝓝 (actualBasinDensity N * (4 / 9))) :=
  oddTerminalFan_weighted_mean (basinIndicator N) m
    (basinIndicator_abs_le_one N) (actual_basin_adjacentVariation N)
    (actual_basin_sourceMean N)

theorem actual_basin_oddTerminalFan_scaled_limit (N m : ℕ) (r : ℝ) :
    Tendsto (fun X : ℕ => (r / (X : ℝ)) *
      (∑ q ∈ Finset.range (32 * X), basinIndicator N q * oddTerminalFan m q))
      atTop (𝓝 ((128 * r / 9) * actualBasinDensity N)) :=
  oddTerminalFan_scaled_source_limit (basinIndicator N) m r
    (basinIndicator_abs_le_one N) (actual_basin_adjacentVariation N)
    (actual_basin_sourceMean N)

#print axioms actual_basin_sourceMean
#print axioms actual_basin_periodic_sourceMean
#print axioms actual_basin_oddTerminalFan_scaled_limit

end CollatzCanonical.PeriodicCensusFloor
