import UnitHaarCylinder
import UnitSourceDensityComparison
import CanonicalSyracLawBridge
import CanonicalPadicCylinderRecursion

/-!
# Actual Haar integrals of the unit-source density error

The finite branch density is lifted by the actual 3-adic residue map.
The comparison density is the existing canonical cylinder density.
Concrete Haar projection and canonical cylinder identities turn the
previous finite estimates into actual full-Haar and unit-Haar integrals.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem canonicalPadicRho_eq_syracMass (k : ℕ) (x : ℤ_[3]) :
    canonicalPadicRho k x =
      (3 : ℝ) ^ k * (syracPMF k (PadicInt.toZModPow k x)).toReal := by
  rw [canonicalPadicRho, canonical_cylinder_real_eq_syracPMF]

/-- The finite, independently defined branch density evaluated on an
actual 3-adic cylinder. -/
noncomputable def unitSourcePadicBranchDensity (j : ℕ) (x : ℤ_[3]) : ℝ :=
  unitSourceBranchDensity j (PadicInt.toZModPow (j + 1) x)

theorem padicThree_cylinder_integrable (μ : Measure ℤ_[3]) [IsFiniteMeasure μ]
    (k : ℕ) (f : ZMod (3 ^ k) → ℝ) :
    Integrable (fun x : ℤ_[3] => f (PadicInt.toZModPow k x)) μ := by
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (padic_projection_measurable k).aemeasurable).mp Integrable.of_finite

theorem canonicalPadicRho_integrable (μ : Measure ℤ_[3]) [IsFiniteMeasure μ]
    (k : ℕ) : Integrable (canonicalPadicRho k) μ := by
  change Integrable (fun x => canonicalPadicRho k x) μ
  simp_rw [canonicalPadicRho_eq_syracMass]
  exact padicThree_cylinder_integrable μ k
    (fun y => (3 : ℝ) ^ k * (syracPMF k y).toReal)

theorem unitSourcePadicBranchDensity_integrable
    (μ : Measure ℤ_[3]) [IsFiniteMeasure μ] (j : ℕ) :
    Integrable (unitSourcePadicBranchDensity j) μ :=
  padicThree_cylinder_integrable μ (j + 1) (unitSourceBranchDensity j)

/-- Equality with the finite error, using the actual additive Haar measure. -/
theorem unitSourcePadic_fullHaar_error_eq_finite (j : ℕ) :
    (∫ x : ℤ_[3], |(3 / 2 : ℝ) * unitSourcePadicBranchDensity j x -
      canonicalPadicRho (j + 1) x| ∂padicThreeHaar) =
      unitSourceFiniteDensityL1Error j := by
  simp_rw [unitSourcePadicBranchDensity, canonicalPadicRho_eq_syracMass]
  exact integral_padicThreeHaar_cylinder (j + 1) (fun y =>
    |(3 / 2 : ℝ) * unitSourceBranchDensity j y -
      (3 : ℝ) ^ (j + 1) * (syracPMF (j + 1) y).toReal|)

theorem exists_unitSourcePadic_fullHaar_error_le_inv_pow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      (∫ x : ℤ_[3], |(3 / 2 : ℝ) * unitSourcePadicBranchDensity j x -
        canonicalPadicRho (j + 1) x| ∂padicThreeHaar) ≤
        C / ((j + 1 : ℕ) : ℝ) ^ A := by
  simpa only [unitSourcePadic_fullHaar_error_eq_finite] using
    exists_unitSourceFiniteDensityL1Error_le_inv_pow A

/-- Equality with the unit-normalized error for the actual Haar restriction. -/
theorem unitSourcePadic_unitHaar_error_eq_finite (j : ℕ) :
    (∫ x : ℤ_[3], |unitSourcePadicBranchDensity j x -
      (2 / 3 : ℝ) * canonicalPadicRho (j + 1) x| ∂padicThreeUnitHaar) =
      unitSourceFiniteUnitDensityL1Error j := by
  simp_rw [unitSourcePadicBranchDensity, canonicalPadicRho_eq_syracMass]
  exact integral_padicThreeUnitHaar_cylinder j (fun y =>
    |unitSourceBranchDensity j y -
      (2 / 3 : ℝ) * ((3 : ℝ) ^ (j + 1) * (syracPMF (j + 1) y).toReal)|)

theorem exists_unitSourcePadic_unitHaar_error_le_inv_pow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      (∫ x : ℤ_[3], |unitSourcePadicBranchDensity j x -
        (2 / 3 : ℝ) * canonicalPadicRho (j + 1) x| ∂padicThreeUnitHaar) ≤
        C / ((j + 1 : ℕ) : ℝ) ^ A := by
  simpa only [unitSourcePadic_unitHaar_error_eq_finite] using
    exists_unitSourceFiniteUnitDensityL1Error_le_inv_pow A

#print axioms canonicalPadicRho_eq_syracMass
#print axioms exists_unitSourcePadic_fullHaar_error_le_inv_pow
#print axioms exists_unitSourcePadic_unitHaar_error_le_inv_pow

end Erdos1135.Tao
