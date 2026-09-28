/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftCensus

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

def ndExplicitQuadraticMixingAt (Cmix : ℝ) (m : ℕ) : Prop :=
  ∀ k : ℕ, ∀ hmk : m ≤ k,
    ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤
        Cmix / (m : ℝ) ^ 2

theorem explicitConductor_error_le_half {P Cmix a : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hsquare : 88 * P * Cmix ≤ a * (m : ℝ) ^ 2) :
    44 * P * (Cmix / (m : ℝ) ^ 2) ≤ a / 2 := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).2
  linarith only [hsquare]

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
