/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorTerminalHighExitAggregation

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem
    ndGeom2PredictableRootSideUniformFloorIncidence_fourPow_mul_root_le_four_mul_threePow_mul_source
    {Label : Type*} {root : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    4 ^ b *
          root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) ≤
      4 * 3 ^ b *
        ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z := by
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hshell :=
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
      hrootOdd (fun _ => hb) hrootLower z
  have hscaled :
      2 ^ r *
            (4 ^ b *
              root
                (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) ≤
        2 ^ r *
          (4 * 3 ^ b *
            ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
    simpa only [r, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hshell.1
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity : 0 < 2 ^ r)

theorem
    ndGeom2PredictableRootSideUniformFloorIncidence_threePow_mul_source_le_twoPow_capSucc_mul_fourPow_mul_root
    {Label : Type*} {root : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    3 ^ b * ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ≤
      2 ^ (K + 1) * 4 ^ b *
        root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) := by
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hshell :=
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
      hrootOdd (fun _ => hb) hrootLower z
  have hscaled :
      2 ^ r *
          (3 ^ b *
            ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) ≤
        2 ^ r *
          (2 ^ (K + 1) * 4 ^ b *
            root
              (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) := by
    simpa only [r, pow_add, pow_one, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hshell.2
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity : 0 < 2 ^ r)

theorem
    ndGeom2PredictableRootSideUnitChildIncidence_fourPow_mul_parent_le_four_mul_threePow_mul_source
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    4 ^ b * root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) ≤
      4 * 3 ^ b * ndGeom2PredictableRootSideUnitChildIncidenceSource z := by
  simpa only [ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_label,
    ndGeom2PredictableRootSideUnitChildIncidenceSource] using
      (ndGeom2PredictableRootSideUniformFloorIncidence_fourPow_mul_root_le_four_mul_threePow_mul_source
        hrootOdd hb hrootLower
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z))

theorem
    ndGeom2PredictableRootSideUnitChildIncidence_threePow_mul_source_le_twoPow_capSucc_mul_fourPow_mul_parent
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ}
    {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 9 ≤ b)
    (hrootLower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) K) :
    3 ^ b * ndGeom2PredictableRootSideUnitChildIncidenceSource z ≤
      2 ^ (K + 1) * 4 ^ b *
        root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := by
  simpa only [ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_label,
    ndGeom2PredictableRootSideUnitChildIncidenceSource] using
      (ndGeom2PredictableRootSideUniformFloorIncidence_threePow_mul_source_le_twoPow_capSucc_mul_fourPow_mul_root
        hrootOdd hb hrootLower
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z))

end

end PositiveDensity

end ND

end Erdos1135Predecessor
