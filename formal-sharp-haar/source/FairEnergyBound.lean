import FairEnergyFinite
import FairEnergyMoments
import FairEnergyLimit
import CanonicalSyracuseCylinderLaw

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

theorem residue_energy_le_quadratic_cubic (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2 ≤
      52 * (k : ℝ) ^ 2 + (52 / 3 : ℝ) * (k : ℝ) ^ 3 := by
  classical
  apply residue_energy_le_of_finite
  intro s
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (2 / (k : ℝ)) * ∑ w ∈ s, cubicMomentTerm k w :=
      finite_residue_energy_le_moment k hk s
    _ ≤ (2 / (k : ℝ)) * ∑' w : GeometricWord k, cubicMomentTerm k w :=
      mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum s (fun w _ => cubicMomentTerm_nonneg k w)
          (cubicMomentTerm_summable k)) (by positivity)
    _ ≤ (2 / (k : ℝ)) *
        (26 * (k : ℝ) ^ 3 + (26 / 3 : ℝ) * (k : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (cubicMomentTerm_tsum_le k) (by positivity)
    _ = _ := by
      field_simp
      ring

theorem residue_energy_lt_seventy_cubic (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2 <
      70 * (k : ℝ) ^ 3 := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hkr)]
  have h3 : (0 : ℝ) < (k : ℝ) ^ 3 := by positivity
  exact (residue_energy_le_quadratic_cubic k hk).trans_lt (by nlinarith)

theorem canonical_cylinder_energy_lt_seventy_cubic (k : ℕ) (hk : 1 ≤ k) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k),
        ((canonicalSyracuseMeasure
          {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal) ^ 2 <
      70 * (k : ℝ) ^ 3 := by
  simp_rw [canonical_cylinder_real]
  exact residue_energy_lt_seventy_cubic k hk

#print axioms residue_energy_le_quadratic_cubic
#print axioms residue_energy_lt_seventy_cubic
#print axioms canonical_cylinder_energy_lt_seventy_cubic

end CollatzCylinderPacking.Arithmetic.FairEnergy
