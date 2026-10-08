/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.Residue
import Erdos1135SecondScale.Tao.Syracuse.ValuationCylinder

/-!
# Syracuse Valuation Cylinder Residues

This module packages a Syracuse valuation tuple as its exact residue class modulo
`2 ^ (taoTupleWeight as + 1)`.  It is the deterministic arithmetic boundary used by later CRT
arguments; no probability or analytic estimates are introduced here.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- The unique residue class whose parity prefix encodes the valuation tuple `as`. -/
noncomputable def syracuseValuationCylinderResidue (as : List ℕ+) :
    ZMod (2 ^ (taoTupleWeight as + 1)) :=
  Classical.choose (existsUnique_residue_syracuseValuationCylinderWord_weight as)

theorem natCast_eq_syracuseValuationCylinderResidue_iff
    (as : List ℕ+) (N : ℕ) :
    (N : ZMod (2 ^ (taoTupleWeight as + 1))) =
        syracuseValuationCylinderResidue as ↔
      Terras.parityPrefixList (taoTupleWeight as + 1) N =
        syracuseValuationCylinderWord as := by
  classical
  unfold syracuseValuationCylinderResidue
  exact (Classical.choose_spec
    (existsUnique_residue_syracuseValuationCylinderWord_weight as)).1 N

/-- An odd integer has valuation tuple `as` exactly when it lies in the associated class modulo
`2 ^ (taoTupleWeight as + 1)`. -/
theorem syracuseValuationPNatList_eq_iff_natCast_eq_cylinderResidue
    (as : List ℕ+) {N : ℕ} (hN : Odd N) :
    syracuseValuationPNatList as.length N hN = as ↔
      (N : ZMod (2 ^ (taoTupleWeight as + 1))) =
        syracuseValuationCylinderResidue as := by
  rw [valuation_eq_iff_parityPrefixList_cylinder as hN]
  exact (natCast_eq_syracuseValuationCylinderResidue_iff as N).symm

end Tao
end Erdos1135SecondScale
