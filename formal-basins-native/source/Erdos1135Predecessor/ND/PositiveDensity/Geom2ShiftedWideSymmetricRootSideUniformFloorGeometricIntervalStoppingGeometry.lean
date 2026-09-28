/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricPhysicalScaleIntervalAdvance
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideUniformFloorTerminalSourceTariff

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem ndGeom2ShiftedWideSymmetric_geometricIntervalOverlap_exponent
    {b K : ℕ} (hb : 600 ≤ b) (hK : K ≤ b / 200) :
    K + 1 + 2 * (b + b / 100) <
      ndGeom2ShiftedWideSymmetricShiftRadius b +
        ndGeom2ShiftedWideSymmetricShiftRadius (b + b / 100) +
          (19 * (b + b / 100)) / 12 := by
  apply ndGeom2ShiftedWideSymmetric_intervalOverlap_exponent
    hb (by omega) hK
  omega

theorem
    ndGeom2ShiftedWideSymmetric_geometricIntervalMin_lt_intervalMax_of_shellUpper
    {b K M N : ℕ} (hb : 600 ≤ b) (hK : K ≤ b / 200)
    (hM : 0 < M)
    (hsourceUpper :
      3 ^ b * N ≤ 2 ^ (K + 1) * 4 ^ b * M) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (b + b / 100) N <
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax b M := by
  let b' := b + b / 100
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let r' := ndGeom2ShiftedWideSymmetricShiftRadius b'
  let L' := (19 * b') / 12
  have hexponent : K + 1 + 2 * b' < r + r' + L' := by
    simpa only [b', r, r', L'] using
      ndGeom2ShiftedWideSymmetric_geometricIntervalOverlap_exponent hb hK
  have hbalancedLower' : 2 ^ L' ≤ 3 ^ b' := by
    simpa only [L'] using
      two_pow_nineteen_mul_div_twelve_le_three_pow b'
  have hscaleExponent :
      2 ^ (K + 1) * 4 ^ b' <
        2 ^ (r + r') * 3 ^ b' := by
    calc
      2 ^ (K + 1) * 4 ^ b' = 2 ^ (K + 1 + 2 * b') := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      _ < 2 ^ (r + r' + L') :=
        Nat.pow_lt_pow_right (by norm_num) hexponent
      _ = 2 ^ (r + r') * 2 ^ L' := by rw [pow_add]
      _ ≤ 2 ^ (r + r') * 3 ^ b' :=
        Nat.mul_le_mul_left (2 ^ (r + r')) hbalancedLower'
  have hcross :
      3 ^ b * (4 ^ b' * N) <
        2 ^ (r + r') * 3 ^ b' * (4 ^ b * M) := by
    calc
      3 ^ b * (4 ^ b' * N) = 4 ^ b' * (3 ^ b * N) := by ring
      _ ≤ 4 ^ b' * (2 ^ (K + 1) * 4 ^ b * M) :=
        Nat.mul_le_mul_left (4 ^ b') hsourceUpper
      _ = (2 ^ (K + 1) * 4 ^ b') * (4 ^ b * M) := by ring
      _ < (2 ^ (r + r') * 3 ^ b') * (4 ^ b * M) := by
        exact (Nat.mul_lt_mul_right (by
          exact mul_pos (pow_pos (by norm_num) _) hM)).2 hscaleExponent
  have hcrossReal :
      ((4 ^ b' * N : ℕ) : ℝ) *
          ((4 * 2 ^ r * 3 ^ b : ℕ) : ℝ) <
        ((2 ^ (2 * r) * 4 ^ b * M : ℕ) : ℝ) *
          ((4 * 2 ^ r' * 3 ^ b' : ℕ) : ℝ) := by
    exact_mod_cast (show
      (4 ^ b' * N) * (4 * 2 ^ r * 3 ^ b) <
        (2 ^ (2 * r) * 4 ^ b * M) * (4 * 2 ^ r' * 3 ^ b') by
      calc
        (4 ^ b' * N) * (4 * 2 ^ r * 3 ^ b) =
            4 * 2 ^ r * (3 ^ b * (4 ^ b' * N)) := by ring
        _ < 4 * 2 ^ r *
            (2 ^ (r + r') * 3 ^ b' * (4 ^ b * M)) := by
          exact (Nat.mul_lt_mul_left (by positivity : 0 < 4 * 2 ^ r)).2
            hcross
        _ = (2 ^ (2 * r) * 4 ^ b * M) *
            (4 * 2 ^ r' * 3 ^ b') := by
          norm_num only [pow_add]
          ring)
  unfold ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
    ndGeom2ShiftedWideSymmetricPhysicalLowerScale
  norm_num only [pow_zero, one_mul]
  change
    ((4 ^ b' * N : ℕ) : ℝ) /
          ((4 * 2 ^ r' * 3 ^ b' : ℕ) : ℝ) <
      ((2 ^ (2 * r) * 4 ^ b * M : ℕ) : ℝ) /
        ((4 * 2 ^ r * 3 ^ b : ℕ) : ℝ)
  exact (div_lt_div_iff₀
    (by positivity : (0 : ℝ) < ((4 * 2 ^ r' * 3 ^ b' : ℕ) : ℝ))
    (by positivity : (0 : ℝ) < ((4 * 2 ^ r * 3 ^ b : ℕ) : ℝ))).2
      hcrossReal

end

end PositiveDensity

end ND

end Erdos1135Predecessor
