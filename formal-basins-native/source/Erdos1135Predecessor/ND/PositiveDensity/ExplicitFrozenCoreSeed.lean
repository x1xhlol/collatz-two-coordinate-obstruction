/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitTerminalVariation
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitVariationBudgets
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftMarkedLoss

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

def explicitSeedFloor (b : ℕ) : ℕ → ℕ
  | 0 => b
  | n + 1 => explicitSeedFloor b n + explicitSeedFloor b n / 100

theorem explicitSeedFloor_bounds (b n : ℕ) :
    b ≤ explicitSeedFloor b n ∧ explicitSeedFloor b n ≤ b * 2 ^ n := by
  induction n with
  | zero => simp [explicitSeedFloor]
  | succ n ih =>
    have hd := Nat.div_le_self (explicitSeedFloor b n) 100
    simp only [explicitSeedFloor, pow_succ]
    constructor
    · omega
    · nlinarith [ih.2]

theorem NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.explicit_forward_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (U.forwardIterate cap n).floor = explicitSeedFloor U.floor n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [U.forwardIterate_succ_eq_next cap n]
    change (U.forwardIterate cap n).floor + (U.forwardIterate cap n).floor / 100 = _
    rw [ih]
    rfl

end

end Erdos1135Predecessor.ND.PositiveDensity
