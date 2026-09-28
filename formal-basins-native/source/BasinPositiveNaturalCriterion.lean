import NativePredecessorMapBridge
import NaturalScalarPrefix

set_option autoImplicit false
open Filter Topology

namespace CollatzCylinderPacking.Arithmetic
open CollatzBasinMapBridges CollatzCanonical.NativeTao

theorem basin_density_ge_positive_count_rate (S : Set ℕ) (N : ℕ) (c : ℝ) (X0 : ℕ)
    (hS : ∀ q ∈ S, 0 < q ∧ basinIndicator N q = 1)
    (hcount : ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤ (Erdos1135Predecessor.Terras.natCount S X : ℝ)) :
    c ≤ actualBasinDensity N := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (actual_basin_natural_density N)
  filter_upwards [eventually_ge_atTop X0, eventually_gt_atTop (0 : ℕ)] with X hX hXpos
  apply (le_div_iff₀ (Nat.cast_pos.mpr hXpos)).mpr
  exact (hcount X hX).trans (native_countBelow_le_basin_prefix S N X hS)

#print axioms basin_density_ge_positive_count_rate

end CollatzCylinderPacking.Arithmetic
