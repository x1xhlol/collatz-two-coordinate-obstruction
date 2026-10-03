import ActualBasinPolynomialFloor
import BasinWeightedDensityComparison

set_option autoImplicit false

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.BoundedInverseSeed CollatzCanonical.GreenKernelScalars

noncomputable section

theorem greenCycleFactor_one_ge_one {N : ℕ} (hN : 0 < N) :
    1 ≤ greenCycleFactor 1 N := by
  classical
  by_cases hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · have hb := positive_cycle_ratio_bounds hN (Nat.find_spec hret).1 (Nat.find_spec hret).2
    simp only [greenCycleFactor, dif_pos hret, Real.rpow_one]
    exact (one_le_inv₀ (sub_pos.mpr hb.2)).mpr (by linarith [hb.1])
  · simp only [greenCycleFactor, dif_neg hret, le_refl]

theorem exists_uniform_firstHit_reciprocal_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → N % 3 ≠ 0 →
      c / (N : ℝ) ≤ actualFirstHitDensity N := by
  obtain ⟨P, hP, hcompare⟩ := actual_basin_and_weighted_density_comparison
  have hPpos : 0 < P := by linarith
  have hKpos : (0 : ℝ) < predecessorSeedMultiplier := by
    exact_mod_cast predecessorSeedMultiplier_pos
  refine ⟨3 / (128 * (predecessorSeedMultiplier : ℝ) * P), by positivity, ?_⟩
  intro N hN hunit
  have hcomp := (hcompare N).2
  rw [mul_comm P] at hcomp
  have h := (div_le_iff₀ hPpos).mpr
    ((actual_basin_polynomial_lower_density hN hunit).trans hcomp)
  convert h using 1
  ring

theorem exists_uniform_unit_canonical_trace_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → N % 3 ≠ 0 →
      c ≤ actualDensityValue actualFirstHitDensity N := by
  obtain ⟨c, hc, hweight⟩ := exists_uniform_firstHit_reciprocal_floor
  refine ⟨delta * c, mul_pos delta_pos hc, ?_⟩
  intro N hN hunit
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hND : c ≤ (N : ℝ) * actualFirstHitDensity N := by
    have h := (div_le_iff₀ hNpos).mp (hweight N hN hunit)
    simpa only [mul_comm] using h
  have hbase := mul_le_mul_of_nonneg_left hND delta_pos.le
  have hDpos := (div_pos hc hNpos).trans_le (hweight N hN hunit)
  have hgamma := mul_le_mul_of_nonneg_left (greenCycleFactor_one_ge_one hN)
    (mul_nonneg delta_pos.le
      (mul_nonneg hNpos.le hDpos.le))
  have htrace : delta * ((N : ℝ) * actualFirstHitDensity N) ≤
      actualDensityValue actualFirstHitDensity N := by
    unfold actualDensityValue
    nlinarith only [hgamma]
  exact hbase.trans htrace

#print axioms greenCycleFactor_one_ge_one
#print axioms exists_uniform_firstHit_reciprocal_floor
#print axioms exists_uniform_unit_canonical_trace_floor

end
end CollatzCanonical.PeriodicCensusFloor
