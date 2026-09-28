/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135Predecessor.Tao.Fourier.MixingStatement
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Section6.UniformLift
import Erdos1135Predecessor.Tao.Syracuse.AffineReverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

def ndSyracuseFullReverseLabelMass
    (q : ℕ) (x : ZMod (3 ^ (q + 1)))
    (y : ZMod (3 ^ q)) (a : ℕ+) : ℝ :=
  if Tao.syracStep q y a = x then
    (Tao.syracPMF q y).toReal * (Tao.geom2PNat a).toReal
  else 0

theorem ndSyracuseFullReverseLabelMass_nonneg
    (q : ℕ) (x : ZMod (3 ^ (q + 1)))
    (y : ZMod (3 ^ q)) (a : ℕ+) :
    0 ≤ ndSyracuseFullReverseLabelMass q x y a := by
  unfold ndSyracuseFullReverseLabelMass
  split_ifs
  · positivity
  · exact le_rfl

def ndSyracuseFullReversePredecessor (u : ℕ) (a : ℕ+) : ℕ :=
  (2 ^ (a : ℕ) * u - 1) / 3

theorem ndSyracuseFullReverseLabel_modEq
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    3 * y.val + 1 ≡ 2 ^ (a : ℕ) * u [MOD 3 ^ (q + 1)] := by
  let p : ZMod (3 ^ (q + 1)) := (2 : ZMod (3 ^ (q + 1))) ^ (a : ℕ)
  have hpinv : p * p⁻¹ = 1 := by
    rw [mul_comm]
    exact Tao.taoZModThreePow_inv_two_pow_mul (q + 1) (a : ℕ)
  have hcast :
      ((3 * y.val + 1 : ℕ) : ZMod (3 ^ (q + 1))) =
        ((2 ^ (a : ℕ) * u : ℕ) : ZMod (3 ^ (q + 1))) := by
    have hstep' : p⁻¹ *
          ((3 : ZMod (3 ^ (q + 1))) *
            (y.val : ZMod (3 ^ (q + 1))) + 1) =
        (u : ZMod (3 ^ (q + 1))) := by
      simpa [p, Tao.syracStep] using hstep
    calc
      ((3 * y.val + 1 : ℕ) : ZMod (3 ^ (q + 1))) =
          (3 : ZMod (3 ^ (q + 1))) *
            (y.val : ZMod (3 ^ (q + 1))) + 1 := by norm_num
      _ = p * (p⁻¹ *
          ((3 : ZMod (3 ^ (q + 1))) *
            (y.val : ZMod (3 ^ (q + 1))) + 1)) := by
            rw [← mul_assoc, hpinv, one_mul]
      _ = p * (u : ZMod (3 ^ (q + 1))) := by rw [hstep']
      _ = ((2 ^ (a : ℕ) * u : ℕ) : ZMod (3 ^ (q + 1))) := by
            simp [p, Nat.cast_pow, Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

theorem ndSyracuseFullReverseLabel_product_modEq_one
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    2 ^ (a : ℕ) * u ≡ 1 [MOD 3] := by
  have hmod := ndSyracuseFullReverseLabel_modEq q u y a hstep
  have hdivpow : 3 ∣ 3 ^ (q + 1) :=
    dvd_pow_self 3 (by omega)
  have hmod3 := hmod.of_dvd hdivpow
  calc
    2 ^ (a : ℕ) * u ≡ 3 * y.val + 1 [MOD 3] := hmod3.symm
    _ ≡ 1 [MOD 3] := by simp [Nat.ModEq]

theorem ndSyracuseFullReverseLabel_target_pos
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    0 < u := by
  have hprod :=
    ndSyracuseFullReverseLabel_product_modEq_one q u y a hstep
  by_contra hu
  have hu0 : u = 0 := Nat.eq_zero_of_not_pos hu
  subst u
  norm_num [Nat.ModEq] at hprod

theorem three_dvd_ndSyracuseFullReverseNumerator
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    3 ∣ 2 ^ (a : ℕ) * u - 1 := by
  have hprod :=
    ndSyracuseFullReverseLabel_product_modEq_one q u y a hstep
  have hu : 0 < u :=
    ndSyracuseFullReverseLabel_target_pos q u y a hstep
  have hpositive : 1 ≤ 2 ^ (a : ℕ) * u :=
    Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.ne_of_gt hu))
  exact Nat.modEq_zero_iff_dvd.mp
    (by simpa using hprod.sub hpositive (by norm_num) Nat.ModEq.rfl)

theorem ndSyracuseFullReversePredecessor_affine
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    2 ^ (a : ℕ) * u =
      3 * ndSyracuseFullReversePredecessor u a + 1 := by
  have hdvd := three_dvd_ndSyracuseFullReverseNumerator q u y a hstep
  unfold ndSyracuseFullReversePredecessor
  have hmul :
      3 * ((2 ^ (a : ℕ) * u - 1) / 3) =
        2 ^ (a : ℕ) * u - 1 := Nat.mul_div_cancel' hdvd
  have hu : 0 < u :=
    ndSyracuseFullReverseLabel_target_pos q u y a hstep
  have hpositive : 1 ≤ 2 ^ (a : ℕ) * u :=
    Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.ne_of_gt hu))
  omega

theorem ndSyracuseFullReversePredecessor_modEq
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    y.val ≡ ndSyracuseFullReversePredecessor u a [MOD 3 ^ q] := by
  have hmod := ndSyracuseFullReverseLabel_modEq q u y a hstep
  have haffine :=
    ndSyracuseFullReversePredecessor_affine q u y a hstep
  have hplus :
      3 * y.val + 1 ≡
        3 * ndSyracuseFullReversePredecessor u a + 1
          [MOD 3 ^ (q + 1)] := by
    simpa [haffine] using hmod
  have hthree :
      3 * y.val ≡ 3 * ndSyracuseFullReversePredecessor u a
        [MOD 3 ^ (q + 1)] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) hplus
  have hpower : 3 ^ (q + 1) = 3 * 3 ^ q := by
    rw [pow_succ']
  rw [hpower] at hthree
  exact Nat.ModEq.mul_left_cancel' (by norm_num) hthree

theorem ndSyracuseFullReversePredecessor_residue
    (q u : ℕ) (y : ZMod (3 ^ q)) (a : ℕ+)
    (hstep : Tao.syracStep q y a =
      (u : ZMod (3 ^ (q + 1)))) :
    (ndSyracuseFullReversePredecessor u a : ZMod (3 ^ q)) = y := by
  rw [← ZMod.natCast_zmod_val y]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (ndSyracuseFullReversePredecessor_modEq q u y a hstep).symm

private theorem ndFullReverse_pmf_bind_apply_toReal_eq_tsum
    {α β : Type*} (p : PMF α) (K : α → PMF β) (z : β) :
    ((p.bind K) z).toReal =
      ∑' u, (p u).toReal * (K u z).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro u
    rw [ENNReal.toReal_mul]
  · intro u
    exact ENNReal.mul_ne_top
      (p.apply_ne_top u) ((K u).apply_ne_top z)

theorem sum_ndSyracuseFullReverseLabelMass_eq_syracPMF
    (q : ℕ) (x : ZMod (3 ^ (q + 1))) :
    (∑ y : ZMod (3 ^ q),
        ∑' a : ℕ+, ndSyracuseFullReverseLabelMass q x y a) =
      (Tao.syracPMF (q + 1) x).toReal := by
  rw [Tao.syracPMF]
  rw [ndFullReverse_pmf_bind_apply_toReal_eq_tsum]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Tao.pmf_map_apply_toReal_tsum]
  unfold ndSyracuseFullReverseLabelMass
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases h : x = Tao.syracStep q y a
  · simp only [h, if_true]
  · have h' : Tao.syracStep q y a ≠ x := by
      exact fun hx => h hx.symm
    simp [h, h']

theorem summable_ndSyracuseFullReverseLabelMass
    (q u : ℕ) (y : ZMod (3 ^ q)) :
    Summable fun a : ℕ+ =>
      ndSyracuseFullReverseLabelMass q
        (u : ZMod (3 ^ (q + 1))) y a := by
  apply Summable.of_nonneg_of_le
  · exact fun a => ndSyracuseFullReverseLabelMass_nonneg q
      (u : ZMod (3 ^ (q + 1))) y a
  · intro a
    unfold ndSyracuseFullReverseLabelMass
    split_ifs
    · exact le_rfl
    · positivity
  · exact (Tao.pmf_summable_toReal Tao.geom2PNat).mul_left
      (Tao.syracPMF q y).toReal

end

end PositiveDensity

end ND

end Erdos1135Predecessor
