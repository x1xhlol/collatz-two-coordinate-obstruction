/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7Character

/-!
# Section 6 Modulus Projection

This leaf exposes reduction from `ZMod (3^T)` to `ZMod (3^r)` and proves
that Tao's source offset projects to its first `r` valuation coordinates.
Inverse powers of `2` are transported through units; no field structure on
the composite-power modulus is assumed.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Canonical reduction from `ZMod (3^T)` to `ZMod (3^r)`. -/
noncomputable def taoZModThreeProjection
    {r T : ℕ} (h : r ≤ T) :
    ZMod (3 ^ T) →+* ZMod (3 ^ r) :=
  ZMod.castHom (Nat.pow_dvd_pow 3 h) (ZMod (3 ^ r))

@[simp]
theorem taoZModThreeProjection_natCast
    {r T : ℕ} (h : r ≤ T) (a : ℕ) :
    taoZModThreeProjection h (a : ZMod (3 ^ T)) =
      (a : ZMod (3 ^ r)) := by
  unfold taoZModThreeProjection
  rw [ZMod.castHom_apply]
  exact ZMod.cast_natCast (Nat.pow_dvd_pow 3 h) a

@[simp]
theorem taoZModThreeProjection_three_pow
    {r T : ℕ} (h : r ≤ T) (i : ℕ) :
    taoZModThreeProjection h
        ((3 : ZMod (3 ^ T)) ^ i) =
      (3 : ZMod (3 ^ r)) ^ i := by
  rw [map_pow]
  exact congrArg (fun z : ZMod (3 ^ r) => z ^ i)
    (taoZModThreeProjection_natCast h 3)

private noncomputable def taoZModThreeTwoUnit
    (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2
    (Nat.Coprime.pow_right n
      (by decide : Nat.Coprime 2 3))

private theorem taoZModThreeTwoUnit_coe (n : ℕ) :
    (taoZModThreeTwoUnit n : ZMod (3 ^ n)) = 2 := by
  simp [taoZModThreeTwoUnit]

private theorem taoZModThreeProjection_twoUnit
    {r T : ℕ} (h : r ≤ T) :
    taoZModThreeProjection h
        (taoZModThreeTwoUnit T : ZMod (3 ^ T)) =
      (taoZModThreeTwoUnit r : ZMod (3 ^ r)) := by
  simpa only [taoZModThreeTwoUnit_coe] using
    (taoZModThreeProjection_natCast h 2)

private theorem taoZModThreeProjection_twoUnit_pow_inv
    {r T : ℕ} (h : r ≤ T) (k : ℕ) :
    taoZModThreeProjection h
        (((taoZModThreeTwoUnit T) ^ k)⁻¹ :
          (ZMod (3 ^ T))ˣ) =
      (((taoZModThreeTwoUnit r) ^ k)⁻¹ :
        (ZMod (3 ^ r))ˣ) := by
  change
    ((Units.map (taoZModThreeProjection h)
        (((taoZModThreeTwoUnit T) ^ k)⁻¹) :
          (ZMod (3 ^ r))ˣ) : ZMod (3 ^ r)) =
      (((taoZModThreeTwoUnit r) ^ k)⁻¹ :
        (ZMod (3 ^ r))ˣ)
  have hu :
      Units.map (taoZModThreeProjection h)
          (taoZModThreeTwoUnit T) =
        taoZModThreeTwoUnit r := by
    apply Units.ext
    exact taoZModThreeProjection_twoUnit h
  rw [map_inv, map_pow, hu]

@[simp]
theorem taoZModThreeProjection_inv_two_pow
    {r T : ℕ} (h : r ≤ T) (k : ℕ) :
    taoZModThreeProjection h
        (((2 : ZMod (3 ^ T)) ^ k)⁻¹) =
      (((2 : ZMod (3 ^ r)) ^ k)⁻¹) := by
  calc
    taoZModThreeProjection h
        (((2 : ZMod (3 ^ T)) ^ k)⁻¹) =
      taoZModThreeProjection h
        (((((taoZModThreeTwoUnit T) ^ k :
            (ZMod (3 ^ T))ˣ) : ZMod (3 ^ T)))⁻¹) := by
          simp [taoZModThreeTwoUnit_coe]
    _ = taoZModThreeProjection h
        (((((taoZModThreeTwoUnit T) ^ k)⁻¹ :
            (ZMod (3 ^ T))ˣ) : ZMod (3 ^ T))) := by
          rw [ZMod.inv_coe_unit]
    _ = (((((taoZModThreeTwoUnit r) ^ k)⁻¹ :
          (ZMod (3 ^ r))ˣ) : ZMod (3 ^ r))) := by
          exact taoZModThreeProjection_twoUnit_pow_inv h k
    _ = (((2 : ZMod (3 ^ r)) ^ k)⁻¹) := by
          rw [← ZMod.inv_coe_unit]
          simp [taoZModThreeTwoUnit_coe]

private theorem taoSection7OffsetSummand_take_of_lt
    (N r : ℕ) (as : List ℕ+) {i : ℕ} (hi : i < r) :
    taoSection7OffsetSummand N (as.take r) i =
      taoSection7OffsetSummand N as i := by
  have hir : i + 1 ≤ r := Nat.succ_le_iff.mpr hi
  simp only [taoSection7OffsetSummand, List.take_take,
    Nat.min_eq_left hir]

private theorem taoSection7OffsetSummand_eq_zero_of_le
    (N : ℕ) (as : List ℕ+) {i : ℕ} (hNi : N ≤ i) :
    taoSection7OffsetSummand N as i = 0 := by
  unfold taoSection7OffsetSummand
  have hpow : (3 : ZMod (3 ^ N)) ^ i = 0 := by
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_pow_eq_zero_of_le 3 hNi)
  rw [hpow, zero_mul]

private theorem taoSection7OffsetSummand_projection
    {r T : ℕ} (h : r ≤ T) (as : List ℕ+) (i : ℕ) :
    taoZModThreeProjection h
        (taoSection7OffsetSummand T as i) =
      taoSection7OffsetSummand r as i := by
  unfold taoSection7OffsetSummand
  rw [map_mul, taoZModThreeProjection_three_pow,
    taoZModThreeProjection_inv_two_pow]

/-- Projecting the level-`T` offset retains exactly its first `r` source
valuations.  No list-length hypothesis is required. -/
theorem taoSection7OffsetZMod_projection_eq_take_of_le
    {r T : ℕ} (h : r ≤ T) (as : List ℕ+) :
    taoZModThreeProjection h
        (taoSection7OffsetZMod T as) =
      taoSection7OffsetZMod r (as.take r) := by
  rw [taoSection7OffsetZMod_eq_offsetPrefix T as]
  rw [taoSection7OffsetZMod_eq_offsetPrefix r (as.take r)]
  unfold taoSection7OffsetPrefix
  rw [map_sum]
  calc
    (∑ i ∈ Finset.range T,
        taoZModThreeProjection h
          (taoSection7OffsetSummand T as i)) =
      ∑ i ∈ Finset.range r,
        taoZModThreeProjection h
          (taoSection7OffsetSummand T as i) := by
        symm
        apply Finset.sum_subset (Finset.range_mono h)
        intro i _hiT hir
        have hri : r ≤ i :=
          Nat.le_of_not_gt
            (fun hi => hir (Finset.mem_range.mpr hi))
        rw [taoSection7OffsetSummand_projection h]
        exact taoSection7OffsetSummand_eq_zero_of_le r as hri
    _ = ∑ i ∈ Finset.range r,
        taoSection7OffsetSummand r as i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact taoSection7OffsetSummand_projection h as i
    _ = ∑ i ∈ Finset.range r,
        taoSection7OffsetSummand r (as.take r) i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact
          (taoSection7OffsetSummand_take_of_lt
            r r as (Finset.mem_range.mp hi)).symm

end

end Tao
end Erdos1135SecondScale
