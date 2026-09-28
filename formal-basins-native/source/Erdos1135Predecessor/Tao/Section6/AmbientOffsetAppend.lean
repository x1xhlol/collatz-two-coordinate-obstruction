/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.AmbientTailDFT

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

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

end

end Tao

end Erdos1135Predecessor
