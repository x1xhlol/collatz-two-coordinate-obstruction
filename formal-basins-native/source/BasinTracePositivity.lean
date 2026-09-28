import MultipleThreeBasinDensity

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic

theorem actual_basin_positive_iff_weighted_positive (N : ℕ) :
    0 < actualBasinDensity N ↔ 0 < actualFirstHitDensity N := by
  obtain ⟨P, hP, hcompare⟩ := actual_basin_and_weighted_density_comparison
  have h := hcompare N
  constructor
  · intro hb
    by_contra hd
    have hd0 := le_of_not_gt hd
    have hprod : P * actualFirstHitDensity N ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hd0
    linarith
  · intro hd
    exact lt_of_lt_of_le hd h.1

theorem actual_weighted_positive_iff_trace_positive {N : ℕ} (hN : 0 < N) :
    0 < actualFirstHitDensity N ↔ 0 < actualDensityValue actualFirstHitDensity N := by
  have hC : 0 < delta * greenCycleFactor 1 N * N :=
    mul_pos (mul_pos delta_pos (greenCycleFactor_one_pos hN)) (Nat.cast_pos.mpr hN)
  change 0 < actualFirstHitDensity N ↔ 0 < (delta * greenCycleFactor 1 N * N) * actualFirstHitDensity N
  exact (mul_pos_iff_of_pos_left hC).symm

theorem actual_density_positivity_equivalences {N : ℕ} (hN : 0 < N) :
    (0 < actualBasinDensity N ↔ 0 < actualFirstHitDensity N) ∧
      (0 < actualFirstHitDensity N ↔ 0 < actualDensityValue actualFirstHitDensity N) :=
  ⟨actual_basin_positive_iff_weighted_positive N, actual_weighted_positive_iff_trace_positive hN⟩

theorem positive_target_reaches_unit {N : ℕ} (hN : 0 < N) :
    ∃ k : ℕ, 0 < iterate k N ∧ (iterate k N) % 3 ≠ 0 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hunit : N % 3 ≠ 0
    · exact ⟨0, hN, hunit⟩
    have hthree : N % 3 = 0 := not_not.mp hunit
    by_cases heven : N % 2 = 0
    · have hhalf : 0 < N / 2 := by omega
      obtain ⟨k, hkpos, hkunit⟩ := ih (N / 2) (Nat.div_lt_self hN (by norm_num)) hhalf
      have hs : step N = N / 2 := by simp only [step, if_pos heven]
      refine ⟨k + 1, ?_, ?_⟩ <;>
        rw [← CollatzBasinMapBridges.iterate_step, hs] <;> assumption
    · have ho : N % 2 = 1 := by omega
      have hs := step_odd ho
      refine ⟨1, ?_, ?_⟩
      · change 0 < step N
        omega
      · change step N % 3 ≠ 0
        omega

#print axioms actual_density_positivity_equivalences
#print axioms positive_target_reaches_unit

end CollatzCylinderPacking.Arithmetic
