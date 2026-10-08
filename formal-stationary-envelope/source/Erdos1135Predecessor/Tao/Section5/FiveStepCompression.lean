/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

theorem three_pow_five_mul_add_le_two_pow_eight_mul_add (q r : ℕ) :
    3 ^ (5 * q + r) ≤ 2 ^ (8 * q + 2 * r) := by
  have hbase : (3 : ℕ) ^ 5 < 2 ^ 8 := by norm_num
  have hblocks : 3 ^ (5 * q) ≤ 2 ^ (8 * q) := by
    have h := Nat.pow_le_pow_left hbase.le q
    simpa only [← Nat.pow_mul] using h
  have hrem : 3 ^ r ≤ 2 ^ (2 * r) := by
    have h := Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ≤ 2 ^ 2) r
    simpa only [← Nat.pow_mul] using h
  calc
    3 ^ (5 * q + r) = 3 ^ (5 * q) * 3 ^ r := by rw [Nat.pow_add]
    _ ≤ 2 ^ (8 * q) * 2 ^ (2 * r) := Nat.mul_le_mul hblocks hrem
    _ = 2 ^ (8 * q + 2 * r) := by rw [Nat.pow_add]

end Tao

end Erdos1135Predecessor
