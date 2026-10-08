/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2OneLawGaussianFirstHitRate

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem two_pow_add_half_le_three_pow (j : ℕ) :
    2 ^ (j + j / 2) ≤ 3 ^ j := by
  let q := j / 2
  let r := j % 2
  have hr : r < 2 := by
    dsimp only [r]
    exact Nat.mod_lt _ (by norm_num)
  have hj : j = 2 * q + r := by
    dsimp only [q, r]
    omega
  have hblock : 8 ^ q ≤ 9 ^ q := Nat.pow_le_pow_left (by norm_num) q
  have htail : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by norm_num) r
  calc
    2 ^ (j + j / 2) = 2 ^ (3 * q + r) := by
      congr 1
      omega
    _ = 2 ^ (3 * q) * 2 ^ r := by rw [pow_add]
    _ = 8 ^ q * 2 ^ r := by
      rw [show 2 ^ (3 * q) = 8 ^ q by
        calc
          2 ^ (3 * q) = (2 ^ 3) ^ q := pow_mul 2 3 q
          _ = 8 ^ q := by norm_num]
    _ ≤ 9 ^ q * 3 ^ r := Nat.mul_le_mul hblock htail
    _ = 3 ^ (2 * q + r) := by
      rw [pow_add]
      rw [show 3 ^ (2 * q) = 9 ^ q by
        calc
          3 ^ (2 * q) = (3 ^ 2) ^ q := pow_mul 3 2 q
          _ = 9 ^ q := by norm_num]
    _ = 3 ^ j := by rw [hj]

theorem add_half_le_ndBalancedTotal (j : ℕ) :
    j + j / 2 ≤ ndBalancedTotal j := by
  have hmono := Nat.clog_monotone 2 (two_pow_add_half_le_three_pow j)
  rw [Nat.clog_pow 2 (j + j / 2) (by norm_num)] at hmono
  exact hmono

end

end PositiveDensity

end ND

end Erdos1135Predecessor
