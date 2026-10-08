/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.DecayStatement
import Erdos1135Predecessor.Tao.Probability.Pascal

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

private noncomputable def prefixWeight (as : List ℕ+) (k : ℕ) : ℕ :=
  taoTupleWeight (as.take k)

noncomputable def taoSection7OffsetZMod (n : ℕ) (as : List ℕ+) : ZMod (3 ^ n) :=
  ∑ i ∈ Finset.range n,
    (3 : ZMod (3 ^ n)) ^ i *
      (((2 : ZMod (3 ^ n)) ^ prefixWeight as (i + 1))⁻¹)

noncomputable def taoSection7OffsetSummand
    (N : ℕ) (as : List ℕ+) (i : ℕ) : ZMod (3 ^ N) :=
  (3 : ZMod (3 ^ N)) ^ i *
    (((2 : ZMod (3 ^ N)) ^ taoTupleWeight (as.take (i + 1)))⁻¹)

noncomputable def taoSection7OffsetPrefix
    (N k : ℕ) (as : List ℕ+) : ZMod (3 ^ N) :=
  ∑ i ∈ Finset.range k, taoSection7OffsetSummand N as i

theorem taoSection7OffsetZMod_eq_offsetPrefix
    (N : ℕ) (as : List ℕ+) :
    taoSection7OffsetZMod N as = taoSection7OffsetPrefix N N as := by
  rfl

private noncomputable def section7CharacterTwoUnit (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right n (by decide : Nat.Coprime 2 3))

private theorem section7CharacterTwoUnit_coe (n : ℕ) :
    (section7CharacterTwoUnit n : ZMod (3 ^ n)) = 2 := by
  simp [section7CharacterTwoUnit]

private theorem section7Character_cast_two_unit (n : ℕ) :
    (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
        (section7CharacterTwoUnit (n + 1) : ZMod (3 ^ (n + 1))) =
      (section7CharacterTwoUnit n : ZMod (3 ^ n)) := by
  rw [section7CharacterTwoUnit_coe, section7CharacterTwoUnit_coe]
  rw [ZMod.castHom_apply]
  exact ZMod.cast_natCast (Nat.pow_dvd_pow 3 (Nat.le_succ n)) 2

private theorem section7Character_cast_two_unit_pow_inv (n k : ℕ) :
    (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
        (((section7CharacterTwoUnit (n + 1)) ^ k)⁻¹ : (ZMod (3 ^ (n + 1)))ˣ) =
      (((section7CharacterTwoUnit n) ^ k)⁻¹ : (ZMod (3 ^ n))ˣ) := by
  change ((Units.map (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
        (((section7CharacterTwoUnit (n + 1)) ^ k)⁻¹) : (ZMod (3 ^ n))ˣ) :
          ZMod (3 ^ n)) =
      (((section7CharacterTwoUnit n) ^ k)⁻¹ : (ZMod (3 ^ n))ˣ)
  have hu : Units.map
      (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
      (section7CharacterTwoUnit (n + 1)) = section7CharacterTwoUnit n := by
    apply Units.ext
    exact section7Character_cast_two_unit n
  rw [map_inv, map_pow, hu]

private theorem section7Character_castHom_inv_two_pow (n k : ℕ) :
    (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
        (((2 : ZMod (3 ^ (n + 1))) ^ k)⁻¹) =
      (((2 : ZMod (3 ^ n)) ^ k)⁻¹) := by
  calc
    (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
        (((2 : ZMod (3 ^ (n + 1))) ^ k)⁻¹)
        = (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
            ((((section7CharacterTwoUnit (n + 1)) ^ k :
                (ZMod (3 ^ (n + 1)))ˣ) : ZMod (3 ^ (n + 1)))⁻¹) := by
            simp [section7CharacterTwoUnit_coe]
    _ = (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
            (((((section7CharacterTwoUnit (n + 1)) ^ k)⁻¹ :
                (ZMod (3 ^ (n + 1)))ˣ) : ZMod (3 ^ (n + 1)))) := by
            rw [ZMod.inv_coe_unit]
    _ = (((((section7CharacterTwoUnit n) ^ k)⁻¹ : (ZMod (3 ^ n))ˣ) :
          ZMod (3 ^ n))) := by
            exact section7Character_cast_two_unit_pow_inv n k
    _ = (((2 : ZMod (3 ^ n)) ^ k)⁻¹) := by
            rw [← ZMod.inv_coe_unit]
            simp [section7CharacterTwoUnit_coe]

private theorem section7Character_castHom_three_pow (n i : ℕ) :
    (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
        ((3 : ZMod (3 ^ (n + 1))) ^ i) =
      ((3 : ZMod (3 ^ n)) ^ i) := by
  rw [map_pow]
  congr 1
  rw [ZMod.castHom_apply]
  exact ZMod.cast_natCast (Nat.pow_dvd_pow 3 (Nat.le_succ n)) 3

private theorem section7Character_cast_highOffset (n : ℕ) (as : List ℕ+) :
    (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n)))
      (∑ i ∈ Finset.range n,
        (3 : ZMod (3 ^ (n + 1))) ^ i *
          (((2 : ZMod (3 ^ (n + 1))) ^ prefixWeight as (i + 1))⁻¹)) =
    taoSection7OffsetZMod n as := by
  unfold taoSection7OffsetZMod
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_mul, section7Character_castHom_three_pow, section7Character_castHom_inv_two_pow]

private theorem section7Character_three_mul_val_eq_three_mul_of_cast_eq
    (n : ℕ) (e : ZMod (3 ^ (n + 1))) (x : ZMod (3 ^ n))
    (h : (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n))) e = x) :
    (3 : ZMod (3 ^ (n + 1))) * (x.val : ZMod (3 ^ (n + 1))) = 3 * e := by
  have hlow : (e.val : ZMod (3 ^ n)) = x := by
    rw [ZMod.castHom_apply] at h
    rw [ZMod.cast_eq_val] at h
    exact h
  have hmod : e.val ≡ x.val [MOD 3 ^ n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [hlow, ZMod.natCast_zmod_val]
  have hmod3 : 3 * e.val ≡ 3 * x.val [MOD 3 ^ (n + 1)] := by
    simpa [pow_succ'] using Nat.ModEq.mul_left' 3 hmod
  rw [← ZMod.natCast_zmod_val e]
  simpa [Nat.cast_mul] using
    (ZMod.natCast_eq_natCast_iff (3 * x.val) (3 * e.val) (3 ^ (n + 1))).mpr
      hmod3.symm

private theorem section7Character_inv_two_pow_add (n a b : ℕ) :
    (((2 : ZMod (3 ^ n)) ^ (a + b))⁻¹) =
      (((2 : ZMod (3 ^ n)) ^ a)⁻¹) * (((2 : ZMod (3 ^ n)) ^ b)⁻¹) := by
  calc
    (((2 : ZMod (3 ^ n)) ^ (a + b))⁻¹)
        = (((((section7CharacterTwoUnit n) ^ (a + b) :
            (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)))⁻¹) := by
            simp [section7CharacterTwoUnit_coe]
    _ = (((((section7CharacterTwoUnit n) ^ (a + b))⁻¹ :
          (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n))) := by
            rw [ZMod.inv_coe_unit]
    _ = (((((section7CharacterTwoUnit n) ^ a)⁻¹ *
          ((section7CharacterTwoUnit n) ^ b)⁻¹ : (ZMod (3 ^ n))ˣ) :
          ZMod (3 ^ n))) := by
            congr 1
            rw [pow_add]
            simp [mul_comm]
    _ = (((2 : ZMod (3 ^ n)) ^ a)⁻¹) * (((2 : ZMod (3 ^ n)) ^ b)⁻¹) := by
            rw [Units.val_mul, ← ZMod.inv_coe_unit, ← ZMod.inv_coe_unit]
            simp [section7CharacterTwoUnit_coe]

private theorem prefixWeight_cons_succ (a : ℕ+) (as : List ℕ+) (i : ℕ) :
    prefixWeight (a :: as) (i + 1) = (a : ℕ) + prefixWeight as i := by
  simp [prefixWeight, taoTupleWeight, List.take_succ_cons]

private theorem prefixWeight_zero (as : List ℕ+) :
    prefixWeight as 0 = 0 := by
  simp [prefixWeight, taoTupleWeight]

theorem taoSection7OffsetZMod_cons
    (n : ℕ) (a : ℕ+) (as : List ℕ+) :
    taoSection7OffsetZMod (n + 1) (a :: as) =
      syracStep n (taoSection7OffsetZMod n as) a := by
  let liftedTail : ZMod (3 ^ (n + 1)) :=
    ∑ i ∈ Finset.range n,
      (3 : ZMod (3 ^ (n + 1))) ^ i *
        (((2 : ZMod (3 ^ (n + 1))) ^ prefixWeight as (i + 1))⁻¹)
  have htailCast :
      (ZMod.castHom (Nat.pow_dvd_pow 3 (Nat.le_succ n)) (ZMod (3 ^ n))) liftedTail =
        taoSection7OffsetZMod n as := by
    simpa [liftedTail] using section7Character_cast_highOffset n as
  have htailVal :
      (3 : ZMod (3 ^ (n + 1))) *
          ((taoSection7OffsetZMod n as).val : ZMod (3 ^ (n + 1))) =
        3 * liftedTail :=
    section7Character_three_mul_val_eq_three_mul_of_cast_eq n liftedTail
      (taoSection7OffsetZMod n as) htailCast
  have hsum :
      (∑ k ∈ Finset.range n,
        (3 : ZMod (3 ^ (n + 1))) ^ (k + 1) *
          ((((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) *
            (((2 : ZMod (3 ^ (n + 1))) ^ prefixWeight as (k + 1))⁻¹))) =
        (3 : ZMod (3 ^ (n + 1))) *
          ((((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) *
            (∑ i ∈ Finset.range n,
              (3 : ZMod (3 ^ (n + 1))) ^ i *
                (((2 : ZMod (3 ^ (n + 1))) ^ prefixWeight as (i + 1))⁻¹))) := by
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [pow_succ']
    ring
  calc
    taoSection7OffsetZMod (n + 1) (a :: as)
        = (((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) +
            (3 : ZMod (3 ^ (n + 1))) *
              ((((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) * liftedTail) := by
            simp [taoSection7OffsetZMod, liftedTail, prefixWeight_cons_succ,
              section7Character_inv_two_pow_add, Finset.sum_range_succ',
              prefixWeight_zero]
            rw [hsum]
            ring
    _ = (((2 : ZMod (3 ^ (n + 1))) ^ (a : ℕ))⁻¹) *
          ((3 : ZMod (3 ^ (n + 1))) *
              ((taoSection7OffsetZMod n as).val : ZMod (3 ^ (n + 1))) + 1) := by
            rw [htailVal]
            ring
    _ = syracStep n (taoSection7OffsetZMod n as) a := by
            rfl

noncomputable def taoSection7CharacterTerm
    (n : ℕ) (ξ : ZMod (3 ^ n)) (as : List ℕ+) : ℂ :=
  taoForwardDFTKernel (taoSection7OffsetZMod n as) ξ

noncomputable def taoSection7SChi (n : ℕ) (ξ : ZMod (3 ^ n)) : ℂ :=
  ∑' as : List ℕ+,
    ((geom2PNatListPMF n as).toReal : ℂ) * taoSection7CharacterTerm n ξ as

def TaoSection7CharacterBridgeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ ξ : ZMod (3 ^ n), zmodThreePrimitive n ξ →
      ZMod.dft (pmfComplexMass (syracPMF n)) ξ = taoSection7SChi n ξ

private theorem taoSection7Char_add {n : ℕ} (ξ x y : ZMod (3 ^ n)) :
    taoForwardDFTKernel (x + y) ξ =
      taoForwardDFTKernel x ξ * taoForwardDFTKernel y ξ := by
  simp only [taoForwardDFTKernel]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem norm_taoForwardDFTKernel {n : ℕ} (x ξ : ZMod (3 ^ n)) :
    ‖taoForwardDFTKernel x ξ‖ = 1 := by
  simp [taoForwardDFTKernel, ZMod.stdAddChar]

noncomputable def taoSection7PairAverage
    (n : ℕ) (ξ x : ZMod (3 ^ n)) : ℂ :=
  (1 / 2 : ℂ) * taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) ξ +
    (1 / 2 : ℂ) * taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) ξ

theorem taoSection7PairAverage_eq_factor
    (n : ℕ) (ξ x : ZMod (3 ^ n)) :
    taoSection7PairAverage n ξ x =
      taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) ξ *
        ((1 / 2 : ℂ) *
          (1 + taoForwardDFTKernel ((2 : ZMod (3 ^ n)) * x) ξ)) := by
  unfold taoSection7PairAverage
  rw [show ((7 : ZMod (3 ^ n)) * x) = (5 : ZMod (3 ^ n)) * x + 2 * x by ring]
  rw [taoSection7Char_add]
  ring

theorem norm_taoSection7PairAverage_eq
    (n : ℕ) (ξ x : ZMod (3 ^ n)) :
    ‖taoSection7PairAverage n ξ x‖ =
      ‖(1 / 2 : ℂ) *
        (1 + taoForwardDFTKernel ((2 : ZMod (3 ^ n)) * x) ξ)‖ := by
  rw [taoSection7PairAverage_eq_factor, norm_mul, norm_taoForwardDFTKernel, one_mul]

end Tao

end Erdos1135Predecessor
