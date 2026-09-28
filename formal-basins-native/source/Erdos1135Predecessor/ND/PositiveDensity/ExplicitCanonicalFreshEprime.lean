/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.HoldListVerticalTail
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeHorizontalTail
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeMarginalMass

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

theorem explicitRenewal_freshEprime_largeBranch
    {J p Aweight fpGap : ℕ} {entry : TaoSection7RenewalPoint}
    {old : TaoSection7Triangle} {horizontalCenter sMin : ℝ}
    (hA : 8 ≤ Aweight) (hpJ : p ≤ J)
    (hgap : old.cornerL - entry.l = (fpGap : ℤ))
    (hcenter : horizontalCenter = entry.toPoint.jReal + (fpGap : ℝ) / 4)
    (hmaster : sMin ^ 2 ≤ 100 * (fpGap : ℝ))
    (hlarge : 30 * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)) ≤ sMin) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
      (lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
        (2 * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)))
        (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)) p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ 112 * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)) / sMin +
        (2 : ℝ) ^ 112 * Real.exp (-(1 / 256 : ℝ) *
          ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)))) := by
  let Xn : ℕ := Aweight ^ 2 * (p + 1)
  let X : ℝ := (Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)
  let E : ℝ := Real.exp (-(1 / 256 : ℝ) * X)
  let Cpoly : ℝ := 270 * (2 : ℝ) ^ 55 / (1 / 65536 : ℝ) ^ 3
  have hXcast : (Xn : ℝ) = X := by dsimp [Xn, X]; push_cast; ring
  have hX : 1 ≤ X := by
    have hA' : (8 : ℝ) ≤ Aweight := by exact_mod_cast hA
    dsimp [X]
    nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p, sq_nonneg ((Aweight : ℝ) - 8)]
  have hXN : 1 ≤ Xn := by exact_mod_cast (show (1 : ℝ) ≤ Xn by rwa [hXcast])
  have hsMin : 1 ≤ sMin := by nlinarith [hX, hlarge]
  have hgapNat : 1 ≤ fpGap := by
    by_contra hn
    have hz : fpGap = 0 := by omega
    rw [hz] at hmaster
    norm_num at hmaster
    nlinarith
  have hthreeFifths : sMin / 16 ≤ (fpGap : ℝ) ^ (3 / 5 : ℝ) :=
    lemma79_sMin_div_sixteen_le_gap_threeFifths (Nat.cast_nonneg fpGap) hsMin hmaster
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hVexp : Real.exp (-(1 / 32 : ℝ) * X) ≤ E := by
    apply Real.exp_le_exp.mpr
    linarith
  have hAexp : Real.exp (-(Real.log (21 / 20 : ℝ) / 8) * X) ≤ E := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right explicitRenewal_log_bounds.1 (by linarith : 0 ≤ X)
    nlinarith
  have hBexp : Real.exp (-(7 / 64 : ℝ) * X) ≤ E := by
    apply Real.exp_le_exp.mpr
    linarith
  have hVpre : (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
      (lemma77CanonicalVerticalOvershootTailEvent fpGap Xn) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 54 * E) := by
    apply (explicitRenewal_verticalTail entry fpGap Xn hXN).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hXcast]
    exact mul_le_mul_of_nonneg_left hVexp (by positivity)
  have hVfresh : (taoSection7HoldListPMF p).toOuterMeasure
      (lemma79CanonicalFreshVerticalTailEvent entry p Xn) ≤ ENNReal.ofReal E := by
    have h := lemma79CanonicalFreshVerticalTailEvent_outerMeasure_le_alphaEighth p Aweight entry hA
    apply (show _ ≤ ENNReal.ofReal (Real.exp (-(Real.log (21 / 20 : ℝ) / 8) * X)) by
      simpa [Xn, X] using h).trans
    exact ENNReal.ofReal_le_ofReal hAexp
  have hHpre : (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
      (lemma77CanonicalHorizontalDeviationEvent fpGap ((fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 112 * X / sMin) := by
    apply (explicitRenewal_threeFifthsTail entry fpGap hgapNat).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Cpoly * X / sMin := lemma79_threeFifthsTail_le_scale
        (by positivity : (0 : ℝ) < 2 ^ 55) (by norm_num : (0 : ℝ) < 1 / 65536)
        hsMin hX hmaster
      _ ≤ (2 : ℝ) ^ 112 * X / sMin := by
        have hc : Cpoly ≤ (2 : ℝ) ^ 112 := by norm_num [Cpoly]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by linarith))
          (by linarith)
  have hHfresh : (taoSection7HoldListPMF p).toOuterMeasure
      (lemma79CanonicalFreshHorizontalTailEvent p ((fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
        ENNReal.ofReal E := by
    have h := lemma79CanonicalFreshHorizontalTailEvent_outerMeasure_le_sevenSixtyFour
      p Aweight fpGap sMin hA hlarge hthreeFifths
    apply (show _ ≤ ENNReal.ofReal (Real.exp (-(7 / 64 : ℝ) * X)) by
      simpa [X] using h).trans
    exact ENNReal.ofReal_le_ofReal hBexp
  have hfour := lemma79CanonicalEndpointFreshEprimeAt_outerMeasure_le_fourMarginals
    (J := J) (p := p) (fpGap := fpGap) (X := Xn) (entry := entry) (old := old)
    (horizontalCenter := horizontalCenter) (t := (fpGap : ℝ) ^ (3 / 5 : ℝ))
    hpJ hgap hcenter
  have hpoly0 : 0 ≤ (2 : ℝ) ^ 112 * X / sMin := by positivity
  have hV0 : 0 ≤ (2 : ℝ) ^ 54 * E := by positivity
  calc
    _ ≤ (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma77CanonicalVerticalOvershootTailEvent fpGap Xn) +
      ((taoSection7HoldListPMF p).toOuterMeasure
        (lemma79CanonicalFreshVerticalTailEvent entry p Xn) +
        ((lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
          (lemma77CanonicalHorizontalDeviationEvent fpGap ((fpGap : ℝ) ^ (3 / 5 : ℝ))) +
          (taoSection7HoldListPMF p).toOuterMeasure
            (lemma79CanonicalFreshHorizontalTailEvent p ((fpGap : ℝ) ^ (3 / 5 : ℝ))))) := by
      simpa [hXcast] using hfour
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 54 * E) +
        (ENNReal.ofReal E + (ENNReal.ofReal ((2 : ℝ) ^ 112 * X / sMin) + ENNReal.ofReal E)) :=
      add_le_add hVpre (add_le_add hVfresh (add_le_add hHpre hHfresh))
    _ = ENNReal.ofReal ((2 : ℝ) ^ 112 * X / sMin + ((2 : ℝ) ^ 54 + 2) * E) := by
      rw [← ENNReal.ofReal_add hpoly0 hE0,
        ← ENNReal.ofReal_add hE0 (add_nonneg hpoly0 hE0),
        ← ENNReal.ofReal_add hV0 (add_nonneg hE0 (add_nonneg hpoly0 hE0))]
      apply congrArg ENNReal.ofReal
      ring
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 112 * X / sMin + (2 : ℝ) ^ 112 * E) := by
      apply ENNReal.ofReal_le_ofReal
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ^ 54 + 2 ≤ 2 ^ 112) hE0

end

end Erdos1135Predecessor.ND.PositiveDensity
