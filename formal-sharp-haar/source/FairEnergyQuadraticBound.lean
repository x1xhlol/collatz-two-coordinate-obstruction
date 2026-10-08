import FairEnergyQuadraticFinite
import FairEnergyLimit
import CanonicalSyracuseCylinderLaw

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

theorem residue_energy_le_linear_quadratic (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2 ≤
      24 * (k : ℝ) + 8 * (k : ℝ) ^ 2 := by
  classical
  apply residue_energy_le_of_finite
  intro s
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (4 / (k : ℝ)) * ∑ w ∈ s, quadraticMomentTerm k w :=
      finite_residue_energy_le_quadratic_moment k hk s
    _ ≤ (4 / (k : ℝ)) * ∑' w : GeometricWord k, quadraticMomentTerm k w :=
      mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum s (fun w _ => quadraticMomentTerm_nonneg k w)
          (quadraticMomentTerm_summable k)) (by positivity)
    _ ≤ (4 / (k : ℝ)) * (6 * (k : ℝ) ^ 2 + 2 * (k : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (quadraticMomentTerm_tsum_le k) (by positivity)
    _ = _ := by
      field_simp
      ring

theorem residue_energy_le_thirtytwo_quadratic (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2 ≤
      32 * (k : ℝ) ^ 2 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  exact (residue_energy_le_linear_quadratic k hk).trans (by nlinarith)

theorem canonical_cylinder_energy_le_thirtytwo_quadratic (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k),
        ((canonicalSyracuseMeasure
          {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal) ^ 2 ≤
      32 * (k : ℝ) ^ 2 := by
  simp_rw [canonical_cylinder_real]
  exact residue_energy_le_thirtytwo_quadratic k hk

#print axioms residue_energy_le_linear_quadratic
#print axioms residue_energy_le_thirtytwo_quadratic
#print axioms canonical_cylinder_energy_le_thirtytwo_quadratic

end CollatzCylinderPacking.Arithmetic.FairEnergy
