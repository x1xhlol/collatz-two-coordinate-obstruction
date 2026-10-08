/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitConductor
import Mathlib.Data.Nat.Log

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

def explicitLogarithmicRoomStart (m : ℕ) : ℕ :=
  200 * (Nat.clog 2 m - 78)

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem explicit_forward_floor_doubling
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (j n : ℕ) (hn : 200 * j ≤ n) :
    U.floor * 2 ^ j ≤ (U.forwardIterate cap n).floor := by
  have htwo : (2 : ℝ) ≤ (201 / 200 : ℝ) ^ 200 := by
    calc
      _ = 1 + (200 : ℝ) * (1 / 200 : ℝ) := by norm_num
      _ ≤ (1 + (1 / 200 : ℝ)) ^ 200 := one_add_mul_le_pow (by norm_num) 200
      _ = _ := by congr 1; norm_num
  have hp : (2 : ℝ) ^ j ≤ (201 / 200 : ℝ) ^ n := by
    calc
      _ ≤ ((201 / 200 : ℝ) ^ 200) ^ j := pow_le_pow_left₀ (by norm_num) htwo j
      _ = (201 / 200 : ℝ) ^ (200 * j) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
  have h := (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg U.floor)).trans
    (U.core_forward_floor_geometric_lower cap n)
  exact_mod_cast h

theorem explicitConductor_logarithmic_quarter_room
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (a m n : ℕ) (ha : 2 ^ a ≤ U.floor)
    (hn : 200 * (Nat.clog 2 m + 2 - a) ≤ n) :
    m ≤ (U.forwardIterate cap n).floor / 4 ∧
      (U.forwardIterate cap n).floor / 4 ≤ (U.forwardIterate cap n).floor := by
  let j := Nat.clog 2 m + 2 - a
  have hj : Nat.clog 2 m + 2 ≤ a + j := by dsimp [j]; omega
  have hfloor := U.explicit_forward_floor_doubling cap j n hn
  have hfour : 4 * m ≤ (U.forwardIterate cap n).floor := by
    calc
      _ ≤ 4 * 2 ^ Nat.clog 2 m := Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) m)
      _ = 2 ^ (Nat.clog 2 m + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (a + j) := Nat.pow_le_pow_right (by decide) hj
      _ = 2 ^ a * 2 ^ j := pow_add _ _ _
      _ ≤ U.floor * 2 ^ j := Nat.mul_le_mul_right _ ha
      _ ≤ _ := hfloor
  exact ⟨by omega, Nat.div_le_self _ _⟩

theorem explicitConductor_logarithmic_quarter_room_eighty
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (m n : ℕ) (hb : 2 ^ 80 ≤ U.floor)
    (hn : explicitLogarithmicRoomStart m ≤ n) :
    m ≤ (U.forwardIterate cap n).floor / 4 ∧
      (U.forwardIterate cap n).floor / 4 ≤ (U.forwardIterate cap n).floor := by
  apply U.explicitConductor_logarithmic_quarter_room cap 80 m n hb
  unfold explicitLogarithmicRoomStart at hn
  have he : Nat.clog 2 m + 2 - 80 = Nat.clog 2 m - 78 := by omega
  rwa [he]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
