/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Affine

namespace Erdos1135Predecessor

namespace Tao

theorem taoOffsetList_nonneg (as : List ℕ+) :
    0 ≤ taoOffsetList as := by
  induction as with
  | nil => simp [taoOffsetList]
  | cons a as ih =>
      rw [taoOffsetList]
      exact add_nonneg
        (div_nonneg (pow_nonneg (by norm_num) _)
          (pow_nonneg (by norm_num) _)) ih

theorem taoOffsetList_le_three_pow_length (as : List ℕ+) :
    taoOffsetList as ≤ (3 : ℚ) ^ as.length := by
  induction as with
  | nil => simp [taoOffsetList]
  | cons a as ih =>
      have hhead :
          (3 : ℚ) ^ as.length /
              (2 : ℚ) ^ taoTupleWeight (a :: as) ≤
            (3 : ℚ) ^ as.length :=
        div_le_self (pow_nonneg (by norm_num) _)
          (one_le_pow₀ (by norm_num))
      calc
        taoOffsetList (a :: as) =
            (3 : ℚ) ^ as.length /
                (2 : ℚ) ^ taoTupleWeight (a :: as) + taoOffsetList as := rfl
        _ ≤ (3 : ℚ) ^ as.length + (3 : ℚ) ^ as.length :=
          add_le_add hhead ih
        _ ≤ (3 : ℚ) ^ (a :: as).length := by
          rw [List.length_cons, pow_succ]
          have hp : 0 ≤ (3 : ℚ) ^ as.length := pow_nonneg (by norm_num) _
          nlinarith

end Tao

end Erdos1135Predecessor
