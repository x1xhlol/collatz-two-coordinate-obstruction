/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase1Threshold
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalOuterBadJTail

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

def explicitRenewalOuterBadJThreshold (A P : ℕ) : ℕ :=
  (2 ^ 38 * A) ^ 2 + 2 ^ 38 * (P + 65)

theorem explicitRenewal_outerBadJ_coefficient (P : ℕ) :
    (2 : ℝ) ^ 55 + Real.exp ((P : ℝ) / 2) ≤ Real.exp ((P : ℝ) + 56) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ 55 ≤ Real.exp 55 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 55
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have ha : (2 : ℝ) ^ 55 ≤ Real.exp ((P : ℝ) + 55) :=
    hp.trans (Real.exp_le_exp.mpr (by linarith))
  have hb : Real.exp ((P : ℝ) / 2) ≤ Real.exp ((P : ℝ) + 55) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 2 * Real.exp ((P : ℝ) + 55) := by linarith
    _ ≤ Real.exp 1 * Real.exp ((P : ℝ) + 55) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem explicitRenewal_outerBadJ_absorption (A P m : ℕ)
    (hm : explicitRenewalOuterBadJThreshold A P ≤ m) :
    (m : ℝ) ^ A * ((2 : ℝ) ^ 55 + Real.exp ((P : ℝ) / 2)) *
      Real.exp (-(1 / 2 ^ 36 : ℝ) * m) ≤ 1 / 2 := by
  have hsmall : (2 ^ 38 * A) ^ 2 ≤ m := by
    exact (Nat.le_add_right _ _).trans hm
  have hroom : 2 ^ 38 * (P + 65) ≤ m := by
    exact (Nat.le_add_left _ _).trans hm
  have hm1 : 1 ≤ m := by
    have hp : 0 < 2 ^ 38 * (P + 65) := by positivity
    exact hp.trans_le hroom
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsquared : ((2 : ℝ) ^ 38 * A) ^ 2 ≤ m := by exact_mod_cast hsmall
  have hsqrt : (2 : ℝ) ^ 38 * A ≤ Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ (2 : ℝ) ^ 38 * A)] using
      Real.sqrt_le_sqrt hsquared
  have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (m : ℝ))
  rw [Real.mul_self_sqrt hmPos.le] at hmul
  have hlog := mul_le_mul_of_nonneg_left (explicitRenewal_log_le_sqrt hmPos)
    (Nat.cast_nonneg (α := ℝ) A)
  have hpoly : (A : ℝ) * Real.log (m : ℝ) ≤ (m : ℝ) / 2 ^ 38 := by
    norm_num at hmul ⊢
    nlinarith
  have hroomReal : (2 : ℝ) ^ 38 * ((P : ℝ) + 65) ≤ m := by exact_mod_cast hroom
  have hArg : (A : ℝ) * Real.log (m : ℝ) + ((P : ℝ) + 56) -
      (1 / 2 ^ 36 : ℝ) * m ≤ -1 := by
    norm_num at hpoly hroomReal ⊢
    linarith
  have hpow : (m : ℝ) ^ A = Real.exp ((A : ℝ) * Real.log (m : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hmPos]
  have hexpHalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos (1 : ℝ))]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (m : ℝ) ^ A * Real.exp ((P : ℝ) + 56) *
        Real.exp (-(1 / 2 ^ 36 : ℝ) * m) := by
      gcongr
      exact explicitRenewal_outerBadJ_coefficient P
    _ = Real.exp ((A : ℝ) * Real.log (m : ℝ) + ((P : ℝ) + 56) -
        (1 / 2 ^ 36 : ℝ) * m) := by
      rw [hpow, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr hArg
    _ ≤ 1 / 2 := hexpHalf

theorem explicitRenewal_outerBadJ_weighted (A P : ℕ)
    {J : ℕ} (hPJ : P ≤ J) (entry : TaoSection7RenewalPoint) (gap m : ℕ)
    (hm : explicitRenewalOuterBadJThreshold A P ≤ m)
    (hgap : (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    (m : ℝ) ^ A *
      ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom | 9 * m ≤ 10 * (atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
      1 / 2 := by
  have hm1 : 1 ≤ m := by
    have hp : 0 < 2 ^ 38 * (P + 65) := by positivity
    exact hp.trans_le ((Nat.le_add_left _ _).trans hm)
  have ht := explicitRenewal_outerBadJ_tail hPJ entry gap m hm1 hgap
  have h := mul_le_mul_of_nonneg_left ht (pow_nonneg (Nat.cast_nonneg m) A)
  exact h.trans (by simpa only [mul_assoc] using explicitRenewal_outerBadJ_absorption A P m hm)

end

end Erdos1135Predecessor.ND.PositiveDensity
