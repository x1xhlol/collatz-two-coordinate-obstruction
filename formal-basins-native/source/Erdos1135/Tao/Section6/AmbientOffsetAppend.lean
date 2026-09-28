import Erdos1135.Tao.Section6.AmbientTailDFT

/-!
# Section 6 Ambient Offset Append

This deterministic leaf splits Tao's fixed-ambient offset across a direct-order
head-tail append and identifies the tail contribution with the normalized
ambient tail embedding.  It introduces no source event or head submass.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
namespace Tao

noncomputable section

private theorem taoSection6_inv_two_pow_add
    (N a b : ℕ) :
    (((2 : ZMod (3 ^ N)) ^ (a + b))⁻¹) =
      (((2 : ZMod (3 ^ N)) ^ a)⁻¹) *
        (((2 : ZMod (3 ^ N)) ^ b)⁻¹) := by
  calc
    (((2 : ZMod (3 ^ N)) ^ (a + b))⁻¹) =
        ((((taoCor63TwoPowUnit N (a + b))⁻¹ :
          (ZMod (3 ^ N))ˣ) : ZMod (3 ^ N))) := by
            rw [← ZMod.inv_coe_unit, taoCor63TwoPowUnit_coe]
    _ = ((((taoCor63TwoPowUnit N a)⁻¹ *
          (taoCor63TwoPowUnit N b)⁻¹ : (ZMod (3 ^ N))ˣ) :
          ZMod (3 ^ N))) := by
            congr 1
            simp [taoCor63TwoPowUnit, pow_add, mul_comm]
    _ = (((2 : ZMod (3 ^ N)) ^ a)⁻¹) *
          (((2 : ZMod (3 ^ N)) ^ b)⁻¹) := by
            rw [Units.val_mul, ← ZMod.inv_coe_unit, ← ZMod.inv_coe_unit]
            simp only [taoCor63TwoPowUnit_coe]

/-- A fixed-ambient offset prefix splits across a direct-order list append.
The tail is scaled by exactly `3^K * 2^(-weight head)`. -/
theorem taoSection7OffsetPrefix_append
    (N K T : ℕ) (head tail : List ℕ+)
    (hhead : head.length = K) :
    taoSection7OffsetPrefix N (K + T) (head ++ tail) =
      taoSection7OffsetPrefix N K head +
        ((3 : ZMod (3 ^ N)) ^ K *
          (((2 : ZMod (3 ^ N)) ^ taoTupleWeight head)⁻¹)) *
        taoSection7OffsetPrefix N T tail := by
  classical
  unfold taoSection7OffsetPrefix
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    unfold taoSection7OffsetSummand
    have hiK : i + 1 ≤ head.length := by
      rw [hhead]
      exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
    rw [List.take_append_of_le_length hiK]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold taoSection7OffsetSummand
    have htake :
        (head ++ tail).take (K + j + 1) =
          head ++ tail.take (j + 1) := by
      rw [show K + j + 1 = head.length + (j + 1) by omega]
      rw [List.take_add]
      simp
    rw [htake, taoTupleWeight_append, taoSection6_inv_two_pow_add]
    rw [pow_add]
    ring

/-- Projecting the first `T` ambient tail summands recovers the level-`T`
offset. -/
theorem taoSection7OffsetPrefix_projection_eq_offsetZMod
    (T K : ℕ) (tail : List ℕ+) :
    taoZModThreeProjection (Nat.le_add_right T K)
        (taoSection7OffsetPrefix (T + K) T tail) =
      taoSection7OffsetZMod T tail := by
  rw [taoSection7OffsetZMod_eq_offsetPrefix]
  unfold taoSection7OffsetPrefix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold taoSection7OffsetSummand
  rw [map_mul, taoZModThreeProjection_three_pow,
    taoZModThreeProjection_inv_two_pow]

/-- Representatives equal after projection modulo `3^T` become equal in the
ambient modulus after multiplication by `3^K`. -/
theorem taoSection6_three_pow_mul_val_eq_three_pow_mul_of_projection_eq
    (T K : ℕ) (e : ZMod (3 ^ (T + K))) (z : ZMod (3 ^ T))
    (hproj : taoZModThreeProjection (Nat.le_add_right T K) e = z) :
    (3 : ZMod (3 ^ (T + K))) ^ K *
        (z.val : ZMod (3 ^ (T + K))) =
      (3 : ZMod (3 ^ (T + K))) ^ K * e := by
  have hlow : (e.val : ZMod (3 ^ T)) = z := by
    calc
      (e.val : ZMod (3 ^ T)) =
          taoZModThreeProjection (Nat.le_add_right T K) e := by
            symm
            exact taoZModThreeProjection_eq_natCast_val
              (Nat.le_add_right T K) e
      _ = z := hproj
  have hmod : e.val ≡ z.val [MOD 3 ^ T] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [hlow, ZMod.natCast_zmod_val]
  have hscaled :
      3 ^ K * e.val ≡ 3 ^ K * z.val [MOD 3 ^ (T + K)] := by
    simpa [pow_add, Nat.mul_comm] using
      Nat.ModEq.mul_left' (3 ^ K) hmod
  rw [← ZMod.natCast_zmod_val e]
  simpa [Nat.cast_mul] using
    (ZMod.natCast_eq_natCast_iff
      (3 ^ K * z.val) (3 ^ K * e.val) (3 ^ (T + K))).mpr
      hscaled.symm

/-- The scaled ambient tail prefix is exactly the committed canonical
representative embedding of the level-`T` offset. -/
theorem taoSection7OffsetTailBlock_eq_ambientTailEmbed
    (K T l : ℕ) (head tail : List ℕ+)
    (hweight : taoTupleWeight head = l) :
    ((3 : ZMod (3 ^ (T + K))) ^ K *
        (((2 : ZMod (3 ^ (T + K))) ^ taoTupleWeight head)⁻¹)) *
        taoSection7OffsetPrefix (T + K) T tail =
      taoSection6AmbientTailEmbed K T l
        (taoSection7OffsetZMod T tail) := by
  have hproj :=
    taoSection7OffsetPrefix_projection_eq_offsetZMod T K tail
  have hscaled :=
    taoSection6_three_pow_mul_val_eq_three_pow_mul_of_projection_eq
      T K (taoSection7OffsetPrefix (T + K) T tail)
        (taoSection7OffsetZMod T tail) hproj
  unfold taoSection6AmbientTailEmbed
  rw [← ZMod.inv_coe_unit, taoCor63TwoPowUnit_coe]
  rw [hweight]
  calc
    ((3 : ZMod (3 ^ (T + K))) ^ K *
        (((2 : ZMod (3 ^ (T + K))) ^ l)⁻¹)) *
        taoSection7OffsetPrefix (T + K) T tail =
      (((2 : ZMod (3 ^ (T + K))) ^ l)⁻¹) *
        ((3 : ZMod (3 ^ (T + K))) ^ K *
          taoSection7OffsetPrefix (T + K) T tail) := by ring
    _ = (((2 : ZMod (3 ^ (T + K))) ^ l)⁻¹) *
        ((3 : ZMod (3 ^ (T + K))) ^ K *
          ((taoSection7OffsetZMod T tail).val :
            ZMod (3 ^ (T + K)))) := by rw [← hscaled]
    _ = (3 : ZMod (3 ^ (T + K))) ^ K *
        (((2 : ZMod (3 ^ (T + K))) ^ l)⁻¹) *
        ((taoSection7OffsetZMod T tail).val :
          ZMod (3 ^ (T + K))) := by ring

/-- Tao's direct-order full offset is the ambient head prefix plus the
normalized ambient tail embedding. -/
theorem taoSection6OffsetZMod_append_eq_head_add_ambientTail
    (K T l : ℕ) (head tail : List ℕ+)
    (hhead : head.length = K)
    (hweight : taoTupleWeight head = l) :
    taoSection7OffsetZMod (T + K) (head ++ tail) =
      taoSection7OffsetPrefix (T + K) K head +
        taoSection6AmbientTailEmbed K T l
          (taoSection7OffsetZMod T tail) := by
  rw [taoSection7OffsetZMod_eq_offsetPrefix]
  calc
    taoSection7OffsetPrefix (T + K) (T + K) (head ++ tail) =
        taoSection7OffsetPrefix (T + K) (K + T) (head ++ tail) := by
          rw [Nat.add_comm]
    _ = taoSection7OffsetPrefix (T + K) K head +
        ((3 : ZMod (3 ^ (T + K))) ^ K *
          (((2 : ZMod (3 ^ (T + K))) ^ taoTupleWeight head)⁻¹)) *
          taoSection7OffsetPrefix (T + K) T tail :=
      taoSection7OffsetPrefix_append (T + K) K T head tail hhead
    _ = taoSection7OffsetPrefix (T + K) K head +
        taoSection6AmbientTailEmbed K T l
          (taoSection7OffsetZMod T tail) := by
      rw [taoSection7OffsetTailBlock_eq_ambientTailEmbed K T l head tail hweight]

/-- With an empty head, the append endpoint recovers the level-`T` offset
through the zero-head ambient embedding. -/
theorem taoSection6OffsetZMod_append_eq_zero_head
    (T : ℕ) (tail : List ℕ+) :
    taoSection7OffsetZMod T ([] ++ tail) =
      taoSection7OffsetPrefix T 0 [] +
        taoSection6AmbientTailEmbed 0 T 0
          (taoSection7OffsetZMod T tail) := by
  simpa [taoTupleWeight] using
    taoSection6OffsetZMod_append_eq_head_add_ambientTail
      0 T 0 ([] : List ℕ+) tail rfl (by simp [taoTupleWeight])

/-- With no tail coordinates, the full offset is exactly the ambient head
prefix. -/
theorem taoSection6OffsetZMod_append_eq_zero_tail
    (K : ℕ) (head tail : List ℕ+)
    (hhead : head.length = K) :
    taoSection7OffsetZMod K (head ++ tail) =
      taoSection7OffsetPrefix K K head := by
  rw [taoSection7OffsetZMod_eq_offsetPrefix]
  unfold taoSection7OffsetPrefix
  apply Finset.sum_congr rfl
  intro i hi
  unfold taoSection7OffsetSummand
  have hiK : i + 1 ≤ head.length := by
    rw [hhead]
    exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
  rw [List.take_append_of_le_length hiK]

/-- A two-coordinate head exposes the exact `3^2 * 2^(-weight head)` tail
coefficient. -/
theorem taoSection7OffsetPrefix_append_two
    (N T : ℕ) (head tail : List ℕ+)
    (hhead : head.length = 2) :
    taoSection7OffsetPrefix N (2 + T) (head ++ tail) =
      taoSection7OffsetPrefix N 2 head +
        ((3 : ZMod (3 ^ N)) ^ 2 *
          (((2 : ZMod (3 ^ N)) ^ taoTupleWeight head)⁻¹)) *
        taoSection7OffsetPrefix N T tail :=
  taoSection7OffsetPrefix_append N 2 T head tail hhead

/-- The direct-order two-variable head prefix is
`2^-a + 3 * 2^-(a+b)`. -/
theorem taoSection7OffsetPrefix_two_values
    (N : ℕ) (a b : ℕ+) :
    taoSection7OffsetPrefix N 2 [a, b] =
      (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) +
        3 * (((2 : ZMod (3 ^ N)) ^ ((a : ℕ) + (b : ℕ)))⁻¹) := by
  simp [taoSection7OffsetPrefix, taoSection7OffsetSummand, taoTupleWeight,
    Finset.sum_range_succ, pow_succ]

end

end Tao
end Erdos1135
