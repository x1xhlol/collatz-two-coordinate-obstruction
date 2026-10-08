/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Syracuse.AffineEnvelope
import Erdos1135SecondScale.Tao.Syracuse.AffineOdd
import Erdos1135SecondScale.Tao.Syracuse.OddSource
import Mathlib.Data.ZMod.Basic

/-!
# Affine Residues And Unique Odd Sources

This neutral leaf identifies the residue compatibility of one Syracuse affine
tuple with existence of exactly one odd natural source.  The construction is
subtraction-free until divisibility and non-underflow have been established.
It contains no Section 5 source window, probability law, tuple reversal, or
common-normalizer argument.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped ZMod

/-- The affine offset residue after dividing by the invertible `2^weight`
factor modulo `3^q`. -/
noncomputable def taoAffineOffsetZMod
    (q : ℕ) (as : List ℕ+) : ZMod (3 ^ q) :=
  (taoOffsetNum as : ZMod (3 ^ q)) *
    (((2 : ZMod (3 ^ q)) ^ taoTupleWeight as)⁻¹)

/-- The natural affine source selected by a compatible tuple and endpoint. -/
def taoAffineSourceCandidate (q : ℕ) (as : List ℕ+) (M : ℕ) : ℕ :=
  (2 ^ taoTupleWeight as * M - taoOffsetNum as) / 3 ^ q

private theorem two_zmod_three_pow_isUnit (q : ℕ) :
    IsUnit (2 : ZMod (3 ^ q)) := by
  simpa using
    (ZMod.unitOfCoprime 2
      (Nat.Coprime.pow_right q (by decide : Nat.Coprime 2 3))).isUnit

private theorem two_pow_zmod_three_pow_isUnit (q S : ℕ) :
    IsUnit ((2 : ZMod (3 ^ q)) ^ S) :=
  (two_zmod_three_pow_isUnit q).pow S

/-- Multiplying by the unit `2^weight` recovers the subtraction-free cleared
residue condition. -/
theorem taoAffineOffsetZMod_eq_iff_cleared
    (q : ℕ) (as : List ℕ+) (M : ℕ) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as ↔
      (((2 ^ taoTupleWeight as * M : ℕ) : ZMod (3 ^ q))) =
        (taoOffsetNum as : ZMod (3 ^ q)) := by
  let a : ZMod (3 ^ q) := (2 : ZMod (3 ^ q)) ^ taoTupleWeight as
  have ha : IsUnit a := two_pow_zmod_three_pow_isUnit q (taoTupleWeight as)
  have hainv : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have hainv' : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  rw [taoAffineOffsetZMod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change (M : ZMod (3 ^ q)) = (taoOffsetNum as : ZMod (3 ^ q)) * a⁻¹ ↔
    a * (M : ZMod (3 ^ q)) = (taoOffsetNum as : ZMod (3 ^ q))
  constructor
  · intro h
    rw [h]
    calc
      a * ((taoOffsetNum as : ZMod (3 ^ q)) * a⁻¹) =
          (taoOffsetNum as : ZMod (3 ^ q)) * (a * a⁻¹) := by ring
      _ = (taoOffsetNum as : ZMod (3 ^ q)) := by rw [hainv, mul_one]
  · intro h
    calc
      (M : ZMod (3 ^ q)) = 1 * (M : ZMod (3 ^ q)) := by rw [one_mul]
      _ = (a⁻¹ * a) * (M : ZMod (3 ^ q)) := by rw [hainv']
      _ = a⁻¹ * (a * (M : ZMod (3 ^ q))) := by ring
      _ = a⁻¹ * (taoOffsetNum as : ZMod (3 ^ q)) := by rw [h]
      _ = (taoOffsetNum as : ZMod (3 ^ q)) * a⁻¹ := by ring

/-- The cleared natural affine offset never exceeds the coarse denominator
times `3^length`. -/
theorem taoOffsetNum_le_two_pow_weight_mul_three_pow_length
    (as : List ℕ+) :
    taoOffsetNum as ≤ 2 ^ taoTupleWeight as * 3 ^ as.length := by
  have hrat :
      (taoOffsetNum as : ℚ) ≤
        ((2 ^ taoTupleWeight as * 3 ^ as.length : ℕ) : ℚ) := by
    calc
      (taoOffsetNum as : ℚ) =
          (2 : ℚ) ^ taoTupleWeight as * taoOffsetList as :=
        (pow_weight_mul_taoOffsetList_eq_num as).symm
      _ ≤ (2 : ℚ) ^ taoTupleWeight as * (3 : ℚ) ^ as.length :=
        mul_le_mul_of_nonneg_left (taoOffsetList_le_three_pow_length as)
          (by positivity)
      _ = ((2 ^ taoTupleWeight as * 3 ^ as.length : ℕ) : ℚ) := by
        norm_num
  exact_mod_cast hrat

/-- For fixed tuple and endpoint, two odd affine sources are equal. -/
theorem taoAffList_oddNat_injective
    (as : List ℕ+) (M : ℕ) {N N' : TaoOddNat}
    (hN : taoAffList as (N.1 : ℚ) = (M : ℚ))
    (hN' : taoAffList as (N'.1 : ℚ) = (M : ℚ)) :
    N = N' := by
  have hclear := (taoAffList_eq_nat_iff_cleared as N.1 M).mp hN
  have hclear' := (taoAffList_eq_nat_iff_cleared as N'.1 M).mp hN'
  have hmul : 3 ^ as.length * N.1 = 3 ^ as.length * N'.1 := by
    omega
  apply Subtype.ext
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) as.length) hmul

/-- Any affine source agrees with the explicit quotient candidate. -/
theorem taoAffineSourceCandidate_eq_of_taoAffList_eq
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q)
    {N M : ℕ} (hAff : taoAffList as (N : ℚ) = (M : ℚ)) :
    taoAffineSourceCandidate q as M = N := by
  have hclear := (taoAffList_eq_nat_iff_cleared as N M).mp hAff
  simp only [taoAffineSourceCandidate]
  rw [← hclear]
  simp [hlen]

/-- Any odd affine source supplies the inverse-normalized affine residue. -/
theorem taoAffineOffsetZMod_eq_of_taoAffList_eq
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q)
    {N : TaoOddNat} {M : ℕ}
    (hAff : taoAffList as (N.1 : ℚ) = (M : ℚ)) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as := by
  have hclear := (taoAffList_eq_nat_iff_cleared as N.1 M).mp hAff
  have hcast := congrArg (fun x : ℕ => (x : ZMod (3 ^ q))) hclear
  apply (taoAffineOffsetZMod_eq_iff_cleared q as M).2
  simpa [hlen] using hcast.symm

/-- Under endpoint room and oddness, affine residue compatibility is
equivalent to existence of exactly one odd natural affine source. -/
theorem taoAffineOffsetZMod_eq_iff_existsUnique_oddNat
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q)
    {M : ℕ} (hM : Odd M) (hroom : 2 * 3 ^ q < M) :
    (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as ↔
      ∃! N : TaoOddNat,
        taoAffList as (N.1 : ℚ) = (M : ℚ) := by
  constructor
  · intro hcompat
    have hclearedZ :=
      (taoAffineOffsetZMod_eq_iff_cleared q as M).mp hcompat
    let S := taoTupleWeight as
    let C := taoOffsetNum as
    let Q := 3 ^ q
    let A := 2 ^ S * M
    have hQpos : 0 < Q := by positivity
    have hQM : Q < M := by
      dsimp only [Q]
      omega
    have hCbound : C ≤ 2 ^ S * Q := by
      dsimp only [C, S, Q]
      simpa only [hlen] using
        taoOffsetNum_le_two_pow_weight_mul_three_pow_length as
    have hpowPos : 0 < 2 ^ S := by positivity
    have hmulRoom : 2 ^ S * Q < 2 ^ S * M :=
      (Nat.mul_lt_mul_left hpowPos).2 hQM
    have hCA : C ≤ A := hCbound.trans (hmulRoom.le)
    have hmod : Nat.ModEq Q A C := by
      dsimp only [Q, A, C, S]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hclearedZ
    have hdiv : Q ∣ A - C :=
      (Nat.modEq_iff_dvd' hCA).mp hmod.symm
    let N := (A - C) / Q
    have hQN : Q * N = A - C := by
      dsimp only [N]
      exact Nat.mul_div_cancel' hdiv
    have hclearNat : Q * N + C = A := by
      rw [hQN, Nat.sub_add_cancel hCA]
    have hclearAff :
        3 ^ as.length * N + taoOffsetNum as =
          2 ^ taoTupleWeight as * M := by
      simpa only [Q, N, A, C, S, hlen] using hclearNat
    have hAff : taoAffList as (N : ℚ) = (M : ℚ) :=
      (taoAffList_eq_nat_iff_cleared as N M).2 hclearAff
    rcases taoAffList_oddNat_decode as N M hM hAff with
      ⟨hNodd, _hvalues, _hiterate⟩
    let Nodd : TaoOddNat := ⟨N, hNodd⟩
    refine ⟨Nodd, ?_, ?_⟩
    · simpa only [Nodd] using hAff
    · intro N' hN'
      exact taoAffList_oddNat_injective as M hN' (by
        simpa only [Nodd] using hAff)
  · rintro ⟨N, hAff, _hunique⟩
    exact taoAffineOffsetZMod_eq_of_taoAffList_eq hlen hAff

/-- Forward projection used by later source-support consumers. -/
theorem existsUnique_taoAffList_eq_of_affineOffsetZMod
    {q : ℕ} {as : List ℕ+} (hlen : as.length = q)
    {M : ℕ} (hM : Odd M) (hroom : 2 * 3 ^ q < M)
    (hcompat : (M : ZMod (3 ^ q)) = taoAffineOffsetZMod q as) :
    ∃! N : TaoOddNat,
      taoAffList as (N.1 : ℚ) = (M : ℚ) :=
  (taoAffineOffsetZMod_eq_iff_existsUnique_oddNat hlen hM hroom).mp hcompat

end

end Tao
end Erdos1135SecondScale
