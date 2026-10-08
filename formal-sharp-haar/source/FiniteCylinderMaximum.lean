import FiniteCylinderResidueLaw
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

noncomputable def maximumResidueMass (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (residueMass k)

theorem maximum_residue_mass_bounds {k : ℕ} (hk : 0 < k) :
    (1 / 2 : ℝ) ^ k ≤ maximumResidueMass k ∧
      maximumResidueMass k ≤ (2 * (k : ℝ) + 3) / (2 : ℝ) ^ k := by
  classical
  constructor
  · exact (residue_mass_lower hk).trans (Finset.le_sup' (f := residueMass k) (Finset.mem_univ (-1)))
  · exact (Finset.sup'_le_iff Finset.univ_nonempty (residueMass k)).mpr
      (fun v _ => residue_mass_upper hk v)

#print axioms maximum_residue_mass_bounds

end CollatzCylinderPacking.Arithmetic
