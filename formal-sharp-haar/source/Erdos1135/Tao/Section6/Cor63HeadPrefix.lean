import Erdos1135.Tao.Section6.Corollary63
import Erdos1135.Tao.Fourier.Section7Character

/-!
# Section 6 Corollary 6.3 Head Prefix

This deterministic leaf identifies the chronological Section 7 head prefix
with the source-facing Corollary 6.3 residue.  The cleared residue carries an
explicit factor `2^l`, which is cancelled only through the existing unit.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
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

/-- The repaired Corollary 6.3 cleared residue is `2^l` times the
chronological Section 7 head prefix. -/
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

/-- The direct-order Section 7 head prefix is exactly the source-facing
Corollary 6.3 residue. -/
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

private theorem taoCor63_offsetPrefix_two_values
    (n : ℕ) (a b : ℕ+) :
    taoSection7OffsetPrefix n 2 [a, b] =
      (((2 : ZMod (3 ^ n)) ^ (a : ℕ))⁻¹) +
        3 * (((2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)))⁻¹) := by
  simp [taoSection7OffsetPrefix, taoSection7OffsetSummand, taoTupleWeight,
    Finset.sum_range_succ, pow_succ]

/-- A one-coordinate source head has residue `2^-a`. -/
theorem taoCor63SourceOffsetZMod_one_value
    (n : ℕ) (a : ℕ+) :
    taoCor63SourceOffsetZMod n (a : ℕ) [a] =
      (((2 : ZMod (3 ^ n)) ^ (a : ℕ))⁻¹) := by
  rw [← taoSection7OffsetPrefix_eq_taoCor63SourceOffsetZMod
    n 1 (a : ℕ) [a] (by simp) (by simp [taoTupleWeight])]
  simp [taoSection7OffsetPrefix, taoSection7OffsetSummand, taoTupleWeight]

/-- A two-coordinate source head preserves chronological order. -/
theorem taoCor63SourceOffsetZMod_two_values
    (n : ℕ) (a b : ℕ+) :
    taoCor63SourceOffsetZMod n ((a : ℕ) + (b : ℕ)) [a, b] =
      (((2 : ZMod (3 ^ n)) ^ (a : ℕ))⁻¹) +
        3 * (((2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)))⁻¹) := by
  rw [← taoSection7OffsetPrefix_eq_taoCor63SourceOffsetZMod
    n 2 ((a : ℕ) + (b : ℕ)) [a, b]
      (by simp) (by simp [taoTupleWeight])]
  exact taoCor63_offsetPrefix_two_values n a b

/-- The two-coordinate cleared residue is `2^b + 3`, exhibiting the factor
`2^(a+b)` between the cleared and source-facing normalizations. -/
theorem taoCor63ClearedOffsetZMod_two_values
    (n : ℕ) (a b : ℕ+) :
    taoCor63ClearedOffsetZMod n ((a : ℕ) + (b : ℕ)) [a, b] =
      (2 : ZMod (3 ^ n)) ^ (b : ℕ) + 3 := by
  rw [taoCor63ClearedOffsetZMod_eq_twoPow_mul_offsetPrefix
    n 2 ((a : ℕ) + (b : ℕ)) [a, b]
      (by simp) (by simp [taoTupleWeight])]
  rw [taoCor63TwoPowUnit_coe, taoCor63_offsetPrefix_two_values]
  rw [mul_add]
  have ha : (a : ℕ) ≤ (a : ℕ) + (b : ℕ) := Nat.le_add_right _ _
  have hab : (a : ℕ) + (b : ℕ) ≤ (a : ℕ) + (b : ℕ) := le_rfl
  rw [show
    (2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)) *
        (((2 : ZMod (3 ^ n)) ^ (a : ℕ))⁻¹) =
      (2 : ZMod (3 ^ n)) ^ (b : ℕ) by
        simpa using taoCor63_two_pow_mul_inv_eq_pow_sub
          n ((a : ℕ) + (b : ℕ)) (a : ℕ) ha]
  rw [show
    (2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)) *
        (3 * (((2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)))⁻¹)) =
      3 by
        calc
          (2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)) *
              (3 * (((2 : ZMod (3 ^ n)) ^
                ((a : ℕ) + (b : ℕ)))⁻¹)) =
            3 * ((2 : ZMod (3 ^ n)) ^ ((a : ℕ) + (b : ℕ)) *
              (((2 : ZMod (3 ^ n)) ^
                ((a : ℕ) + (b : ℕ)))⁻¹)) := by ring
          _ = 3 * (2 : ZMod (3 ^ n)) ^
              (((a : ℕ) + (b : ℕ)) - ((a : ℕ) + (b : ℕ))) := by
                rw [taoCor63_two_pow_mul_inv_eq_pow_sub
                  n ((a : ℕ) + (b : ℕ)) ((a : ℕ) + (b : ℕ)) hab]
          _ = 3 := by simp]

end

end Tao
end Erdos1135
