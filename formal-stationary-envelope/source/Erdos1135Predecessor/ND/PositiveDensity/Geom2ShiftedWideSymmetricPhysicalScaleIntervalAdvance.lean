/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricPhysicalScaleIntervalOverlap

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

private theorem four_mul_six_pow_le_sixtyFour_pow
    {b : ℕ} (hb : 1 ≤ b) :
    4 * 6 ^ b ≤ 64 ^ b := by
  have hsix : 6 ^ b ≤ 16 ^ b :=
    Nat.pow_le_pow_left (by norm_num) b
  have hfour : 4 ≤ 4 ^ b := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) hb
    simpa only [pow_one] using hpow
  calc
    4 * 6 ^ b ≤ 4 * 16 ^ b := Nat.mul_le_mul_left 4 hsix
    _ ≤ 4 ^ b * 16 ^ b := Nat.mul_le_mul_right (16 ^ b) hfour
    _ = 64 ^ b := by rw [← mul_pow]; norm_num

theorem twoPow_base_le_ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
    {b root : ℕ} (hb : 1 ≤ b) (hroot : 16 ^ b ≤ root) :
    ((2 ^ b : ℕ) : ℝ) ≤
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax b root := by
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hr : 2 ^ r ≤ 2 ^ (2 * r) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hscale : 4 * 6 ^ b ≤ 64 ^ b :=
    four_mul_six_pow_le_sixtyFour_pow hb
  have hnat :
      2 ^ b * (4 * 2 ^ r * 3 ^ b) ≤
        2 ^ (2 * r) * 4 ^ b * root := by
    calc
      2 ^ b * (4 * 2 ^ r * 3 ^ b) =
          2 ^ r * (4 * 6 ^ b) := by
        rw [show 6 ^ b = 2 ^ b * 3 ^ b by
          rw [← mul_pow]
          norm_num]
        ring
      _ ≤ 2 ^ (2 * r) * 64 ^ b := Nat.mul_le_mul hr hscale
      _ = 2 ^ (2 * r) * (4 ^ b * 16 ^ b) := by
        rw [← mul_pow]
        norm_num
      _ ≤ 2 ^ (2 * r) * (4 ^ b * root) := by
        gcongr
      _ = 2 ^ (2 * r) * 4 ^ b * root := by ring
  unfold ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
    ndGeom2ShiftedWideSymmetricPhysicalLowerScale
  change
    ((2 ^ b : ℕ) : ℝ) ≤
      ((2 ^ (2 * r) * 4 ^ b * root : ℕ) : ℝ) /
        ((4 * 2 ^ r * 3 ^ b : ℕ) : ℝ)
  apply (le_div_iff₀
    (by positivity : (0 : ℝ) < ((4 * 2 ^ r * 3 ^ b : ℕ) : ℝ))).2
  exact_mod_cast hnat

end

end PositiveDensity

end ND

end Erdos1135Predecessor
