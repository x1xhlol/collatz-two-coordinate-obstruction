import Erdos1135.Tao.Fourier.DecayStatement
import Erdos1135.Tao.Probability.Pascal

set_option backward.isDefEq.respectTransparency false

/-!
# Section 7 Character Surface

This module records the statement-only bridge between Tao's Section 7 character
sum `S_chi(n)` and the existing primitive-frequency DFT surface.  It proves no
Fourier decay and no source bridge from the recursive `syracPMF` definition.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
namespace Tao

private noncomputable def prefixWeight (as : List ℕ+) (k : ℕ) : ℕ :=
  taoTupleWeight (as.take k)

/--
The argument of Tao's Section 7 character sum, equation (7.2), reduced in
`ZMod (3^n)`.

For a valuation list `as = [a_1, ..., a_n]`, this is
`sum_{i=0}^{n-1} 3^i * 2^{-a_[1,i+1]}`.
-/
noncomputable def taoSection7OffsetZMod (n : ℕ) (as : List ℕ+) : ZMod (3 ^ n) :=
  ∑ i ∈ Finset.range n,
    (3 : ZMod (3 ^ n)) ^ i *
      (((2 : ZMod (3 ^ n)) ^ prefixWeight as (i + 1))⁻¹)

/-- One fixed-modulus summand in Tao's Section 7 offset. -/
noncomputable def taoSection7OffsetSummand
    (N : ℕ) (as : List ℕ+) (i : ℕ) : ZMod (3 ^ N) :=
  (3 : ZMod (3 ^ N)) ^ i *
    (((2 : ZMod (3 ^ N)) ^ taoTupleWeight (as.take (i + 1)))⁻¹)

/-- The first `k` offset summands, all evaluated in the fixed ambient modulus
`3^N`. -/
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

/-- The Section 7 offset obeys the same cons recursion as `syracPMF`. -/
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

/--
The source character value `chi_{n,xi}` applied to the Section 7 offset.

The sign and product order cite the project-local DFT convention spine in
`Fourier.Basic` through `taoForwardDFTKernel`.
-/
noncomputable def taoSection7CharacterTerm
    (n : ℕ) (ξ : ZMod (3 ^ n)) (as : List ℕ+) : ℂ :=
  taoForwardDFTKernel (taoSection7OffsetZMod n as) ξ

/--
Tao's Section 7 character expectation `S_chi(n)`, expressed through the checked
exact-length iid positive `Geom(2)` list PMF.
-/
noncomputable def taoSection7SChi (n : ℕ) (ξ : ZMod (3 ^ n)) : ℂ :=
  ∑' as : List ℕ+,
    ((geom2PNatListPMF n as).toReal : ℂ) * taoSection7CharacterTerm n ξ as

/--
Statement target for the source bridge from the recursive `syracPMF` DFT
coefficient to the Section 7 character expectation.
-/
def TaoSection7CharacterBridgeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ ξ : ZMod (3 ^ n), zmodThreePrimitive n ξ →
      ZMod.dft (pmfComplexMass (syracPMF n)) ξ = taoSection7SChi n ξ

/-- Polynomial decay statement for Tao Proposition 7.1 in the `S_chi` vocabulary. -/
def taoSection7CharacterPolynomialDecayAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ ξ : ZMod (3 ^ n), zmodThreePrimitive n ξ →
      ‖taoSection7SChi n ξ‖ ≤ C / (n : ℝ) ^ A

/-- Statement-shaped target corresponding to Tao Proposition 7.1. -/
def TaoProp71CharacterDecayStatement : Prop :=
  ∀ A : ℕ, 0 < A →
    ∃ C : ℝ, 0 ≤ C ∧ taoSection7CharacterPolynomialDecayAt A C

theorem TaoProp71CharacterDecayStatement.bound
    (h : TaoProp71CharacterDecayStatement)
    {A : ℕ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ taoSection7CharacterPolynomialDecayAt A C :=
  h A hA

/--
If the Section 7 character bridge is proved, then Tao's Proposition 7.1
statement implies the current primitive-frequency Proposition 1.17 surface.
-/
theorem TaoProp117PrimitivePolynomialDecayStatement.of_section7_character
    (hbridge : TaoSection7CharacterBridgeStatement)
    (h71 : TaoProp71CharacterDecayStatement) :
    TaoProp117PrimitivePolynomialDecayStatement := by
  intro A hA
  rcases h71 A hA with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro n hn ξ hξ
  rw [hbridge n hn ξ hξ]
  exact hC n hn ξ hξ

/-- Section 7's finite pilot cites the shared R5 DFT convention spine. -/
theorem tao_dft_pmfComplexMass_apply_syracPMF_one (ξ : ZMod (3 ^ 1)) :
    ZMod.dft (pmfComplexMass (syracPMF 1)) ξ =
      ∑ x : ZMod (3 ^ 1),
        taoForwardDFTKernel x ξ * (((syracPMF 1 x).toReal : ℝ) : ℂ) :=
  tao_dft_pmfComplexMass_apply (syracPMF 1) ξ

/-- At level `n = 1`, an even positive valuation contributes residue `1`. -/
theorem taoSection7OffsetZMod_one_even (k : ℕ) :
    taoSection7OffsetZMod 1 [⟨2 * k + 2, by omega⟩] = (1 : ZMod (3 ^ 1)) := by
  simp [taoSection7OffsetZMod, prefixWeight, taoTupleWeight]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
  change (4 : ZMod 3) ^ (k + 1) = 1
  rw [show (4 : ZMod 3) = 1 by decide]
  simp

/-- At level `n = 1`, an odd positive valuation contributes residue `2`. -/
theorem taoSection7OffsetZMod_one_odd (k : ℕ) :
    taoSection7OffsetZMod 1 [⟨2 * k + 1, by omega⟩] = (2 : ZMod (3 ^ 1)) := by
  simp [taoSection7OffsetZMod, prefixWeight, taoTupleWeight]
  have heven : (2 : ZMod (3 ^ 1)) ^ (2 * k) = 1 := by
    rw [pow_mul]
    change (4 : ZMod 3) ^ k = 1
    rw [show (4 : ZMod 3) = 1 by decide]
    simp
  have hpow : (2 : ZMod (3 ^ 1)) ^ (2 * k + 1) = 2 := by
    calc
      (2 : ZMod (3 ^ 1)) ^ (2 * k + 1)
          = (2 : ZMod (3 ^ 1)) ^ (2 * k) * 2 := by
            exact pow_succ (2 : ZMod (3 ^ 1)) (2 * k)
      _ = 1 * 2 := by rw [heven]
      _ = 2 := by norm_num
  rw [hpow]
  change ((2 : ZMod 3)⁻¹ = 2)
  exact inv_eq_of_mul_eq_one_right (by decide : (2 : ZMod 3) * 2 = 1)

theorem taoSection7CharacterTerm_one_even (k : ℕ) (ξ : ZMod (3 ^ 1)) :
    taoSection7CharacterTerm 1 ξ [⟨2 * k + 2, by omega⟩] =
      taoForwardDFTKernel 1 ξ := by
  simp [taoSection7CharacterTerm, taoSection7OffsetZMod_one_even k]

theorem taoSection7CharacterTerm_one_odd (k : ℕ) (ξ : ZMod (3 ^ 1)) :
    taoSection7CharacterTerm 1 ξ [⟨2 * k + 1, by omega⟩] =
      taoForwardDFTKernel 2 ξ := by
  simp [taoSection7CharacterTerm, taoSection7OffsetZMod_one_odd k]

/--
The landed `Syrac(Z/3Z)` DFT table is exactly the even/odd split predicted by
the Section 7 character surface.
-/
theorem dft_syracPMF_one_apply_table_section7_terms (ξ : ZMod (3 ^ 1)) :
    ZMod.dft (pmfComplexMass (syracPMF 1)) ξ =
      taoSection7CharacterTerm 1 ξ [⟨2, by norm_num⟩] • (((1 / 3 : ℝ) : ℂ)) +
        taoSection7CharacterTerm 1 ξ [⟨1, by norm_num⟩] • (((2 / 3 : ℝ) : ℂ)) := by
  rw [dft_syracPMF_one_apply_table]
  rw [taoSection7CharacterTerm_one_even 0, taoSection7CharacterTerm_one_odd 0]
  simp [taoForwardDFTKernel]

private theorem taoSection7Char_add {n : ℕ} (ξ x y : ZMod (3 ^ n)) :
    taoForwardDFTKernel (x + y) ξ =
      taoForwardDFTKernel x ξ * taoForwardDFTKernel y ξ := by
  simp only [taoForwardDFTKernel]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem norm_taoForwardDFTKernel {n : ℕ} (x ξ : ZMod (3 ^ n)) :
    ‖taoForwardDFTKernel x ξ‖ = 1 := by
  change ‖(ZMod.toCircle (-(x * ξ)) : ℂ)‖ = 1
  exact Circle.norm_coe _

/-- The two-point conditional average from Tao equation (7.4) at `b = 3`. -/
noncomputable def taoSection7PairAverage
    (n : ℕ) (ξ x : ZMod (3 ^ n)) : ℂ :=
  (1 / 2 : ℂ) * taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) ξ +
    (1 / 2 : ℂ) * taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) ξ

/--
Algebraic part of Lemma 7.2: after conditioning on `b = 3`, the two-point
average factors as `chi(5x) / 2 * (1 + chi(2x))`.
-/
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

/--
The prefactor `chi(5x)` has norm one, so Lemma 7.2's local bound reduces to
controlling `|1 + chi(2x)| / 2`.
-/
theorem norm_taoSection7PairAverage_eq
    (n : ℕ) (ξ x : ZMod (3 ^ n)) :
    ‖taoSection7PairAverage n ξ x‖ =
      ‖(1 / 2 : ℂ) *
        (1 + taoForwardDFTKernel ((2 : ZMod (3 ^ n)) * x) ξ)‖ := by
  rw [taoSection7PairAverage_eq_factor, norm_mul, norm_taoForwardDFTKernel, one_mul]

end Tao
end Erdos1135
