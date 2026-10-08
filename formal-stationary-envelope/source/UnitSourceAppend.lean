import UnitSourceTailDecay

/-!
# Seeded head-tail arithmetic

These identities retain the terminal affine seed under projection and split
the length-n presentation across a native head of length q. The explicit
positive-tail hypothesis ensures that the unused final exponent is in the
tail, so no retained head coordinate is discarded.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

private theorem unitSource_inv_two_pow_add (N a b : ℕ) :
    (((2 : ZMod (3 ^ N)) ^ (a + b))⁻¹) =
      (((2 : ZMod (3 ^ N)) ^ a)⁻¹) * (((2 : ZMod (3 ^ N)) ^ b)⁻¹) := by
  calc
    _ = ((((taoCor63TwoPowUnit N (a + b))⁻¹ :
        (ZMod (3 ^ N))ˣ) : ZMod (3 ^ N))) := by
      rw [← ZMod.inv_coe_unit, taoCor63TwoPowUnit_coe]
    _ = ((((taoCor63TwoPowUnit N a)⁻¹ *
        (taoCor63TwoPowUnit N b)⁻¹ : (ZMod (3 ^ N))ˣ) : ZMod (3 ^ N))) := by
      congr 1
      simp [taoCor63TwoPowUnit, pow_add, mul_comm]
    _ = _ := by
      rw [Units.val_mul, ← ZMod.inv_coe_unit, ← ZMod.inv_coe_unit]
      simp only [taoCor63TwoPowUnit_coe]

/-- Projection preserves the retained affine seed at any fixed step count. -/
theorem unitSourceAffineOffset_projection
    {r N : ℕ} (hrN : r ≤ N) (k : ℕ)
    (z : ZMod (3 ^ N)) (as : List ℕ+) :
    taoZModThreeProjection hrN (unitSourceAffineOffset N k z as) =
      unitSourceAffineOffset r k (taoZModThreeProjection hrN z) as := by
  unfold unitSourceAffineOffset
  rw [map_add, map_mul, map_mul, taoZModThreeProjection_three_pow]
  rw [taoSection7TwoZPow_neg_nat_eq_inv_pow,
    taoZModThreeProjection_inv_two_pow, taoSection7TwoZPow_neg_nat_eq_inv_pow]
  congr 1
  unfold taoSection7OffsetPrefix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold taoSection7OffsetSummand
  rw [map_mul, taoZModThreeProjection_three_pow, taoZModThreeProjection_inv_two_pow]

/-- The actual affine offset splits into its head and the scaled affine tail. -/
theorem unitSourceAffineOffset_append
    (N q k : ℕ) (z : ZMod (3 ^ N)) (head tail : List ℕ+)
    (hhead : head.length = q) :
    unitSourceAffineOffset N (q + k) z (head ++ tail) =
      taoSection7OffsetPrefix N q head +
        ((3 : ZMod (3 ^ N)) ^ q *
          (((2 : ZMod (3 ^ N)) ^ taoTupleWeight head)⁻¹)) *
        unitSourceAffineOffset N k z tail := by
  unfold unitSourceAffineOffset
  rw [taoSection7OffsetPrefix_append N q k head tail hhead,
    taoTupleWeight_append, taoSection7TwoZPow_neg_nat_eq_inv_pow,
    taoSection7TwoZPow_neg_nat_eq_inv_pow, unitSource_inv_two_pow_add, pow_add]
  ring

theorem unitSourceAffineTailBlock_eq_embed
    (q T l : ℕ) (z : ZMod (3 ^ (T + q))) (tail : List ℕ+) :
    ((3 : ZMod (3 ^ (T + q))) ^ q *
        (((2 : ZMod (3 ^ (T + q))) ^ l)⁻¹)) *
      unitSourceAffineOffset (T + q) (T - 1) z tail =
      taoSection6AmbientTailEmbed q T l
        (unitSourceAffineOffset T (T - 1)
          (taoZModThreeProjection (Nat.le_add_right T q) z) tail) := by
  have hproj := unitSourceAffineOffset_projection
    (Nat.le_add_right T q) (T - 1) z tail
  have hscaled := taoSection6_three_pow_mul_val_eq_three_pow_mul_of_projection_eq
    T q (unitSourceAffineOffset (T + q) (T - 1) z tail)
      (unitSourceAffineOffset T (T - 1)
        (taoZModThreeProjection (Nat.le_add_right T q) z) tail) hproj
  unfold taoSection6AmbientTailEmbed
  rw [← ZMod.inv_coe_unit, taoCor63TwoPowUnit_coe]
  calc
    _ = (((2 : ZMod (3 ^ (T + q))) ^ l)⁻¹) *
        ((3 : ZMod (3 ^ (T + q))) ^ q *
          unitSourceAffineOffset (T + q) (T - 1) z tail) := by ring
    _ = (((2 : ZMod (3 ^ (T + q))) ^ l)⁻¹) *
        ((3 : ZMod (3 ^ (T + q))) ^ q *
          ((unitSourceAffineOffset T (T - 1)
            (taoZModThreeProjection (Nat.le_add_right T q) z) tail).val :
              ZMod (3 ^ (T + q)))) := by rw [← hscaled]
    _ = _ := by ring

/-- The unused final exponent stays in the tail. The positive-tail hypothesis
ensures no head coordinate is discarded. -/
theorem unitSourceLengthNMap_append
    (q T l : ℕ) (hT : 1 ≤ T) (z : ZMod (3 ^ (T + q)))
    (head tail : List ℕ+) (hhead : head.length = q)
    (hweight : taoTupleWeight head = l) :
    unitSourceLengthNMap (T + q) z (head ++ tail) =
      taoSection7OffsetPrefix (T + q) q head +
        taoSection6AmbientTailEmbed q T l
          (unitSourceLengthNMap T (taoZModThreeProjection (Nat.le_add_right T q) z) tail) := by
  have hindex : T + q - 1 = q + (T - 1) := by omega
  have htake : (head ++ tail).take (T + q - 1) = head ++ tail.take (T - 1) := by
    rw [hindex, ← hhead, List.take_add]
    simp
  unfold unitSourceLengthNMap
  rw [htake, hindex, unitSourceAffineOffset_append (T + q) q (T - 1) z
    head (tail.take (T - 1)) hhead, hweight, unitSourceAffineTailBlock_eq_embed]

end Erdos1135.Tao
