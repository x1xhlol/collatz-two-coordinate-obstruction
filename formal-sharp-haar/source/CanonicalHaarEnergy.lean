import FairEnergyBound
import FairEnergyQuadraticBound
import PadicHaarCylinder
import CanonicalPadicCylinderRecursion
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem canonicalPadicRho_memLp (k : ℕ) (p : ℝ≥0∞) :
    MemLp (canonicalPadicRho k) p padicThreeHaar := by
  have hmeas : Measurable (canonicalPadicRho k) := by
    unfold canonicalPadicRho
    exact (measurable_of_countable (fun v : ZMod (3 ^ k) =>
      (3 : ℝ) ^ k * (canonicalSyracuseMeasure
        {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal)).comp
          (padic_projection_measurable k)
  apply MemLp.of_bound hmeas.aestronglyMeasurable ((3 : ℝ) ^ k)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold canonicalPadicRho; positivity)]
  unfold canonicalPadicRho
  have hm : (canonicalSyracuseMeasure
      {y : ℤ_[3] | PadicInt.toZModPow k y = PadicInt.toZModPow k x}).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by
      simpa using (measure_mono (μ := canonicalSyracuseMeasure) (Set.subset_univ
        {y : ℤ_[3] | PadicInt.toZModPow k y = PadicInt.toZModPow k x})))
  simpa using mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 3 ^ k)

theorem canonicalPadicRho_sq_integral_eq_energy (k : ℕ) :
    (∫ x : ℤ_[3], (canonicalPadicRho k x) ^ 2 ∂padicThreeHaar) =
      (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2 := by
  unfold canonicalPadicRho
  simp_rw [canonical_cylinder_real]
  rw [integral_padicThreeHaar_cylinder k
    (fun v => ((3 : ℝ) ^ k * residueMass k v) ^ 2)]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  field_simp

theorem canonicalPadicRho_sq_integral_le_quadratic_cubic (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℤ_[3], (canonicalPadicRho k x) ^ 2 ∂padicThreeHaar) ≤
      52 * (k : ℝ) ^ 2 + (52 / 3 : ℝ) * (k : ℝ) ^ 3 := by
  rw [canonicalPadicRho_sq_integral_eq_energy]
  exact FairEnergy.residue_energy_le_quadratic_cubic k hk

theorem canonicalPadicRho_sq_integral_lt_seventy_cubic (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℤ_[3], (canonicalPadicRho k x) ^ 2 ∂padicThreeHaar) <
      70 * (k : ℝ) ^ 3 := by
  rw [canonicalPadicRho_sq_integral_eq_energy]
  exact FairEnergy.residue_energy_lt_seventy_cubic k hk

theorem canonicalPadicRho_sq_integral_le_linear_quadratic (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℤ_[3], (canonicalPadicRho k x) ^ 2 ∂padicThreeHaar) ≤
      24 * (k : ℝ) + 8 * (k : ℝ) ^ 2 := by
  rw [canonicalPadicRho_sq_integral_eq_energy]
  exact FairEnergy.residue_energy_le_linear_quadratic k hk

theorem canonicalPadicRho_sq_integral_le_thirtytwo_quadratic (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℤ_[3], (canonicalPadicRho k x) ^ 2 ∂padicThreeHaar) ≤
      32 * (k : ℝ) ^ 2 := by
  rw [canonicalPadicRho_sq_integral_eq_energy]
  exact FairEnergy.residue_energy_le_thirtytwo_quadratic k hk

#print axioms canonicalPadicRho_memLp
#print axioms canonicalPadicRho_sq_integral_lt_seventy_cubic
#print axioms canonicalPadicRho_sq_integral_le_thirtytwo_quadratic

end Erdos1135.Tao
