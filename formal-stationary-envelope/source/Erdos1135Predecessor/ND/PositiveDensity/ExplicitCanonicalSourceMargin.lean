/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeSourceMargin

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

theorem explicitRenewal_log_margin_bounds :
    (5 / 16 : ℝ) ≤ Real.log 2 / Real.log 9 ∧
      Real.log 2 / Real.log 9 ≤ (2 / 5 : ℝ) := by
  refine ⟨?_, taoSection7_log2_div_log9_lt_two_fifths.le⟩
  have hlog9 : 0 < Real.log (9 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (9 : ℝ) ^ 5 < (2 : ℝ) ^ 16 := by norm_num
  have h := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at h
  apply (le_div_iff₀ hlog9).mpr
  norm_num at h
  linarith

theorem explicitRenewal_threeFifths_le_linear {S : ℝ} (hS : (2 : ℝ) ^ 20 ≤ S) :
    S ^ (3 / 5 : ℝ) ≤ S / 256 := by
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ 20) hS
    (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)] at hp
  norm_num at hp
  have hprod : S ^ (3 / 5 : ℝ) * S ^ (2 / 5 : ℝ) = S := by
    rw [← Real.rpow_add hS0]
    norm_num
  have h := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hS0.le (3 / 5 : ℝ))
  rw [hprod] at h
  linarith

theorem explicitRenewal_sourceMargin {Pmax fpGap p : ℕ}
    (hgap : 2 ^ 34 * (Pmax + 1) ≤ fpGap) (hp : p ≤ Pmax) :
    2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
      ((Real.log 2 / Real.log 9) * (2 * lemma79OutsideEprimeScale 8192 p) + 1) ≤
        (fpGap : ℝ) * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  have hbig : (2 : ℝ) ^ 34 * ((Pmax : ℝ) + 1) ≤ fpGap := by exact_mod_cast hgap
  have hP : (0 : ℝ) ≤ Pmax := Nat.cast_nonneg Pmax
  have hsmall : (2 : ℝ) ^ 20 ≤ fpGap := by norm_num only at hbig ⊢; nlinarith
  have hJ := explicitRenewal_threeFifths_le_linear hsmall
  have hscale : lemma79OutsideEprimeScale 8192 p ≤
      (2 : ℝ) ^ 26 * ((Pmax : ℝ) + 1) := by
    have hp' : (p : ℝ) ≤ Pmax := by exact_mod_cast hp
    unfold lemma79OutsideEprimeScale lemma79OutsideEprimeScaleNat
    push_cast
    norm_num
    linarith
  have hscale0 : 0 ≤ lemma79OutsideEprimeScale 8192 p := by
    unfold lemma79OutsideEprimeScale lemma79OutsideEprimeScaleNat
    positivity
  have hLmul := mul_le_mul_of_nonneg_right explicitRenewal_log_margin_bounds.2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hscale0)
  have hL : (Real.log 2 / Real.log 9) * (2 * lemma79OutsideEprimeScale 8192 p) + 1 ≤
      (fpGap : ℝ) / 32 := by
    norm_num only at hbig hscale
    nlinarith
  have hmargin := mul_le_mul_of_nonneg_left explicitRenewal_log_margin_bounds.1
    (Nat.cast_nonneg fpGap)
  apply lemma79OutsideEprimeErrorMargin_of_split_absorption
  · nlinarith [show (0 : ℝ) ≤ fpGap from Nat.cast_nonneg fpGap]
  · nlinarith

end

end Erdos1135Predecessor.ND.PositiveDensity
