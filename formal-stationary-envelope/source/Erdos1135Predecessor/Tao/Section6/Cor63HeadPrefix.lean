/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7Character
import Erdos1135Predecessor.Tao.Section6.Corollary63

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

private theorem taoCor63_two_pow_mul_inv_eq_pow_sub
    (n l w : ℕ) (hw : w ≤ l) :
    (2 : ZMod (3 ^ n)) ^ l *
        (((2 : ZMod (3 ^ n)) ^ w)⁻¹) =
      (2 : ZMod (3 ^ n)) ^ (l - w) := by
  have hunit :
      taoCor63TwoPowUnit n l =
        taoCor63TwoPowUnit n (l - w) * taoCor63TwoPowUnit n w := by
    apply Units.ext
    simp only [Units.val_mul, taoCor63TwoPowUnit_coe]
    rw [← pow_add, Nat.sub_add_cancel hw]
  calc
    (2 : ZMod (3 ^ n)) ^ l *
        (((2 : ZMod (3 ^ n)) ^ w)⁻¹) =
      (taoCor63TwoPowUnit n l : ZMod (3 ^ n)) *
        (((taoCor63TwoPowUnit n w)⁻¹ :
          (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) := by
            rw [← ZMod.inv_coe_unit]
            simp only [taoCor63TwoPowUnit_coe]
    _ = (taoCor63TwoPowUnit n (l - w) : ZMod (3 ^ n)) := by
          rw [hunit, Units.val_mul]
          simp
    _ = (2 : ZMod (3 ^ n)) ^ (l - w) :=
      taoCor63TwoPowUnit_coe n (l - w)

theorem taoCor63ClearedOffsetZMod_eq_twoPow_mul_offsetPrefix
    (n q l : ℕ) (head : List ℕ+)
    (hhead : head.length = q)
    (hweight : taoTupleWeight head = l) :
    taoCor63ClearedOffsetZMod n l head =
      (taoCor63TwoPowUnit n l : ZMod (3 ^ n)) *
        taoSection7OffsetPrefix n q head := by
  unfold taoCor63ClearedOffsetZMod
  rw [taoCor63ClearedOffsetSum_eq_range_sum]
  rw [Nat.cast_sum]
  unfold taoSection7OffsetPrefix
  rw [Finset.mul_sum]
  rw [← hhead]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold taoCor63ClearedSummand taoSection7OffsetSummand
  rw [taoSection6IntervalWeight_zero_eq_tupleWeight_take]
  push_cast
  rw [taoCor63TwoPowUnit_coe]
  have hw : taoTupleWeight (head.take (i + 1)) ≤ l := by
    exact (taoTupleWeight_take_le head (i + 1)).trans_eq hweight
  calc
    (3 : ZMod (3 ^ n)) ^ i *
        (2 : ZMod (3 ^ n)) ^
          (l - taoTupleWeight (head.take (i + 1))) =
      (3 : ZMod (3 ^ n)) ^ i *
        ((2 : ZMod (3 ^ n)) ^ l *
          (((2 : ZMod (3 ^ n)) ^
            taoTupleWeight (head.take (i + 1)))⁻¹)) := by
              rw [taoCor63_two_pow_mul_inv_eq_pow_sub n l
                (taoTupleWeight (head.take (i + 1))) hw]
    _ = (2 : ZMod (3 ^ n)) ^ l *
        ((3 : ZMod (3 ^ n)) ^ i *
          (((2 : ZMod (3 ^ n)) ^
            taoTupleWeight (head.take (i + 1)))⁻¹)) := by ring

theorem taoSection7OffsetPrefix_eq_taoCor63SourceOffsetZMod
    (n q l : ℕ) (head : List ℕ+)
    (hhead : head.length = q)
    (hweight : taoTupleWeight head = l) :
    taoSection7OffsetPrefix n q head =
      taoCor63SourceOffsetZMod n l head := by
  unfold taoCor63SourceOffsetZMod
  rw [taoCor63ClearedOffsetZMod_eq_twoPow_mul_offsetPrefix
    n q l head hhead hweight]
  simp

end

end Tao

end Erdos1135Predecessor
