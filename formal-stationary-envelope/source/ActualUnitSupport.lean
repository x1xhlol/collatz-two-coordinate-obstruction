import BasinPositiveNaturalCriterion
import CollatzPredecessorDensity

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic
open CollatzBasinMapBridges

theorem actual_basin_density_pos_of_unit {N : ℕ} (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    0 < actualBasinDensity N := by
  have hdouble : ¬ 3 ∣ 2 * N := by omega
  obtain ⟨c, hc, X0, hcount⟩ :=
    CollatzPredecessorDensity.predecessors_positive_lower_density
      (a := 2 * N) (by omega) hdouble
  have hS : ∀ q ∈ CollatzPredecessorDensity.predecessors (2 * N),
      0 < q ∧ basinIndicator N q = 1 := by
    intro q hq
    exact ⟨hq.1, native_predecessor_double_basin hq.2⟩
  exact hc.trans_le (basin_density_ge_positive_count_rate _ N c X0 hS hcount)

theorem actual_basin_density_positive_iff_unit {N : ℕ} (hN : 0 < N) :
    0 < actualBasinDensity N ↔ N % 3 ≠ 0 := by
  constructor
  · intro hp hz
    rw [actual_basin_density_zero_of_multiple_three hz] at hp
    exact (lt_irrefl 0) hp
  · exact actual_basin_density_pos_of_unit hN

theorem actual_weighted_density_positive_iff_unit {N : ℕ} (hN : 0 < N) :
    0 < actualFirstHitDensity N ↔ N % 3 ≠ 0 :=
  (actual_basin_positive_iff_weighted_positive N).symm.trans
    (actual_basin_density_positive_iff_unit hN)

theorem actual_trace_positive_iff_unit {N : ℕ} (hN : 0 < N) :
    0 < actualDensityValue actualFirstHitDensity N ↔ N % 3 ≠ 0 :=
  (actual_weighted_positive_iff_trace_positive hN).symm.trans
    (actual_weighted_density_positive_iff_unit hN)

#print axioms actual_basin_density_positive_iff_unit
#print axioms actual_weighted_density_positive_iff_unit
#print axioms actual_trace_positive_iff_unit

end CollatzCylinderPacking.Arithmetic
