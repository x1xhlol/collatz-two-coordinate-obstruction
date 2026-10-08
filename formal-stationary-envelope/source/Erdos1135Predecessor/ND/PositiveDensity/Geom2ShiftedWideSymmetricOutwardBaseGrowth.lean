/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricBoundedOvershootPhysicalIncidence

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem ten_mul_ndGeom2ShiftedWideSymmetricShiftRadius_le_three_mul_add_five
    {b : ℕ} (hb : 200 ≤ b) :
    10 * ndGeom2ShiftedWideSymmetricShiftRadius b ≤ 3 * b + 5 := by
  let w := ndGeom2ShiftedWideSymmetricWidth b
  let m := ndGeom2ShiftedWideSymmetricMarginNat b
  let c := ndBalancedTotal w
  let g := ndGeom2ShiftedWideSymmetricGap b
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hcLower : w + w / 2 ≤ c := by
    simpa only [c] using add_half_le_ndBalancedTotal w
  have hgap : g + c = 2 * w := by
    dsimp only [g, c, w]
    unfold ndGeom2ShiftedWideSymmetricGap
    exact Nat.sub_add_cancel
      (ndBalancedTotal_le_two_mul
        (ndGeom2ShiftedWideSymmetricWidth b))
  have hr : r + 2 * m = g := by
    simpa only [r, g, m] using
      ndGeom2ShiftedWideSymmetricShiftRadius_add_two_margin hb
  have hw : 5 * w ≤ 3 * b := by
    dsimp only [w]
    unfold ndGeom2ShiftedWideSymmetricWidth
    omega
  omega

theorem
    ndGeom2ShiftedWideSymmetric_outwardGrowth_exponent_budget
    {b : ℕ} (hb : 200 ≤ b) :
    2 + ndGeom2ShiftedWideSymmetricShiftRadius b +
          ndBalancedTotal b + 4 * (b + b / 100) ≤
      6 * b := by
  have hr :=
    ten_mul_ndGeom2ShiftedWideSymmetricShiftRadius_le_three_mul_add_five hb
  have hc := five_mul_ndBalancedTotal_le_eight_mul_add_five b
  have hq := Nat.div_mul_le_self b 100
  omega

theorem
    four_mul_twoPowShiftRadius_mul_threePow_mul_sixteenPow_base_add_oneHundredth_le_sixtyFourPow
    {b : ℕ} (hb : 200 ≤ b) :
    4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
          16 ^ (b + b / 100) ≤
      64 ^ b := by
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let c := ndBalancedTotal b
  have hthree : 3 ^ b ≤ 2 ^ c := by
    simpa only [c] using three_pow_le_two_pow_ndBalancedTotal b
  have hexp : 2 + r + c + 4 * (b + b / 100) ≤ 6 * b := by
    simpa only [r, c] using
      ndGeom2ShiftedWideSymmetric_outwardGrowth_exponent_budget hb
  calc
    4 * 2 ^ r * 3 ^ b * 16 ^ (b + b / 100) ≤
        4 * 2 ^ r * 2 ^ c * 16 ^ (b + b / 100) := by
      gcongr
    _ = 2 ^ (2 + r + c + 4 * (b + b / 100)) := by
      norm_num only [pow_add, pow_mul]
    _ ≤ 2 ^ (6 * b) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 64 ^ b := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, pow_mul]

end

end PositiveDensity

end ND

end Erdos1135Predecessor
