/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.OffsetInjectivity
import Mathlib.Data.ZMod.Basic

/-!
# Neutral Affine Reversal Identities

This leaf owns deterministic list-reversal identities for Syracuse affine
weights and offsets.  It has no Section 5, Section 6, PMF, or Fourier
dependency.
-/

namespace Erdos1135SecondScale
namespace Tao

@[simp] theorem taoTupleWeight_nil : taoTupleWeight [] = 0 := by
  rfl

@[simp] theorem taoTupleWeight_cons (a : ℕ+) (as : List ℕ+) :
    taoTupleWeight (a :: as) = (a : ℕ) + taoTupleWeight as := by
  simp [taoTupleWeight]

theorem taoTupleWeight_reverse (as : List ℕ+) :
    taoTupleWeight as.reverse = taoTupleWeight as := by
  unfold taoTupleWeight
  simp only [List.map_eq_flatMap]
  induction as with
  | nil => simp
  | cons a as ih =>
      simp [List.reverse_cons, List.flatMap_append, Nat.add_comm]
      simpa [List.map_eq_flatMap] using ih

theorem taoTupleWeight_append (xs ys : List ℕ+) :
    taoTupleWeight (xs ++ ys) = taoTupleWeight xs + taoTupleWeight ys := by
  simp [taoTupleWeight, List.map_append]

theorem taoOffsetList_append (xs ys : List ℕ+) :
    taoOffsetList (xs ++ ys) =
      ((3 : ℚ) ^ ys.length / (2 : ℚ) ^ taoTupleWeight ys) *
        taoOffsetList xs + taoOffsetList ys := by
  induction xs with
  | nil => simp [taoOffsetList]
  | cons a xs ih =>
      rw [List.cons_append, taoOffsetList, ih]
      rw [taoOffsetList]
      have h2y : (2 : ℚ) ^ taoTupleWeight ys ≠ 0 :=
        pow_ne_zero _ (by norm_num)
      have h2x : (2 : ℚ) ^ taoTupleWeight xs ≠ 0 :=
        pow_ne_zero _ (by norm_num)
      have h2a : (2 : ℚ) ^ (a : ℕ) ≠ 0 :=
        pow_ne_zero _ (by norm_num)
      simp [taoTupleWeight, List.map_append, List.length_append, pow_add]
      field_simp [h2y, h2x, h2a]
      ring

theorem taoOffsetList_reverse_cons (a : ℕ+) (as : List ℕ+) :
    taoOffsetList (a :: as).reverse =
      ((1 : ℚ) + 3 * taoOffsetList as.reverse) / (2 : ℚ) ^ (a : ℕ) := by
  rw [List.reverse_cons, taoOffsetList_append]
  simp [taoOffsetList, taoTupleWeight]
  ring

theorem pow_mul_taoOffsetList_reverse_cons (a : ℕ+) (as : List ℕ+) :
    (2 : ℚ) ^ (a : ℕ) * taoOffsetList (a :: as).reverse =
      (1 : ℚ) + 3 * taoOffsetList as.reverse := by
  rw [taoOffsetList_reverse_cons]
  field_simp [pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)]

/-- Cleared affine numerators distribute over list append. -/
theorem taoOffsetNum_append (xs ys : List ℕ+) :
    taoOffsetNum (xs ++ ys) =
      3 ^ ys.length * taoOffsetNum xs +
        2 ^ taoTupleWeight xs * taoOffsetNum ys := by
  induction xs with
  | nil => simp [taoOffsetNum, taoTupleWeight]
  | cons a xs ih =>
      simp [taoOffsetNum, taoTupleWeight, ih, List.length_append, pow_add]
      ring_nf

/-- Appending the first valuation at the right of a reversed tail gives the
cleared affine recurrence used by the Section 7 orientation bridge. -/
theorem taoOffsetNum_reverse_cons (a : ℕ+) (as : List ℕ+) :
    taoOffsetNum (a :: as).reverse =
      2 ^ taoTupleWeight as + 3 * taoOffsetNum as.reverse := by
  rw [List.reverse_cons, taoOffsetNum_append]
  simp [taoOffsetNum, taoTupleWeight_reverse, Nat.add_comm]

private noncomputable def affineReverseTwoUnit (n : ℕ) :
    (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2
    (Nat.Coprime.pow_right n (by decide : Nat.Coprime 2 3))

private theorem affineReverseTwoUnit_coe (n : ℕ) :
    (affineReverseTwoUnit n : ZMod (3 ^ n)) = 2 := by
  simp [affineReverseTwoUnit]

/-- In modulus `3^n`, inverse powers of two split across exponent addition. -/
theorem taoZModThreePow_inv_two_pow_add (n a b : ℕ) :
    (((2 : ZMod (3 ^ n)) ^ (a + b))⁻¹) =
      (((2 : ZMod (3 ^ n)) ^ a)⁻¹) *
        (((2 : ZMod (3 ^ n)) ^ b)⁻¹) := by
  calc
    (((2 : ZMod (3 ^ n)) ^ (a + b))⁻¹) =
        (((((affineReverseTwoUnit n) ^ (a + b) :
          (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)))⁻¹) := by
            simp [affineReverseTwoUnit_coe]
    _ = (((((affineReverseTwoUnit n) ^ (a + b))⁻¹ :
          (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n))) := by
            rw [ZMod.inv_coe_unit]
    _ = (((((affineReverseTwoUnit n) ^ a)⁻¹ *
          ((affineReverseTwoUnit n) ^ b)⁻¹ : (ZMod (3 ^ n))ˣ) :
          ZMod (3 ^ n))) := by
            congr 1
            rw [pow_add]
            simp [mul_comm]
    _ = (((2 : ZMod (3 ^ n)) ^ a)⁻¹) *
          (((2 : ZMod (3 ^ n)) ^ b)⁻¹) := by
            rw [Units.val_mul, ← ZMod.inv_coe_unit, ← ZMod.inv_coe_unit]
            simp [affineReverseTwoUnit_coe]

/-- Powers of two are units modulo `3^n`, so their chosen inverses cancel. -/
theorem taoZModThreePow_inv_two_pow_mul (n a : ℕ) :
    (((2 : ZMod (3 ^ n)) ^ a)⁻¹) *
        ((2 : ZMod (3 ^ n)) ^ a) = 1 := by
  let u : (ZMod (3 ^ n))ˣ := (affineReverseTwoUnit n) ^ a
  have hu : (u : ZMod (3 ^ n)) = (2 : ZMod (3 ^ n)) ^ a := by
    simp [u, affineReverseTwoUnit_coe]
  rw [← hu, ZMod.inv_coe_unit]
  change ((↑(u⁻¹ * u) : ZMod (3 ^ n))) = 1
  simp

end Tao
end Erdos1135SecondScale
