/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorUnitChildTerminalPrefixCode

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

theorem ndGeom2PredictableRootSideUnitChildIncidence_source_mul_weight_le_parent
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b a K : ℕ} (outerWeight : Label → ℝ)
    (hweight : ∀ i ∈ Labels, 0 ≤ outerWeight i)
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence
      Labels root b a K) :
    (ndGeom2PredictableRootSideUnitChildIncidenceSource z : ℝ) *
        ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z ≤
      (root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) : ℝ) *
        outerWeight (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := by
  let physical :=
    ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z
  let i := ndGeom2PredictableRootSideUnitChildIncidenceLabel z
  have hwi : 0 ≤ outerWeight i := hweight z.1.1 z.1.2
  have hedge :=
    ndGeom2PredictableRootSideBoundedOvershootIncidence_source_mul_atom_le_root
      hrootOdd (fun _ => hb) hrootLower physical
  change
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource physical : ℝ) *
        (outerWeight i *
          ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom physical) ≤
      (root i : ℝ) * outerWeight i
  calc
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource physical : ℝ) *
          (outerWeight i *
            ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom physical) =
        outerWeight i *
          ((ndGeom2PredictableRootSideBoundedOvershootIncidenceSource physical : ℝ) *
            ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom physical) := by
      ring
    _ ≤ outerWeight i * (root i : ℝ) :=
      mul_le_mul_of_nonneg_left hedge hwi
    _ = (root i : ℝ) * outerWeight i := by ring

end

end PositiveDensity

end ND

end Erdos1135Predecessor
