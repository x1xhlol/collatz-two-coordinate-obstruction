/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135SecondScale.Tao.Renewal.HoldListVerticalTail
import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEprimeHorizontalTail
import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEprimeMarginalMass

/-!
# Canonical Eprime Large-Branch Bound

This proof leaf assembles the four canonical `E'_p` marginal tails in the
large branch of Tao's `(7.61)`.  The first-passage horizontal tail is absorbed
into `X / sMin`; the other three tails share one positive exponential rate.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

private theorem lemma79_fourTailLargeBranch_scalar
    {Kv cv Kh ch X sMin : ℝ}
    (hKv : 0 < Kv) (hcv : 0 < cv)
    (hKh : 0 < Kh) (hch : 0 < ch)
    (hX : 1 ≤ X) (hsMin : 1 ≤ sMin) :
    let alpha := Real.log (21 / 20 : ℝ) / 8
    let beta := (7 / 64 : ℝ)
    let c := min cv (min alpha beta)
    let Cpoly := 270 * Kh / ch ^ 3
    let Cexp := Kv + 2
    let C := max Cpoly Cexp
    Cpoly * X / sMin +
        (Kv * Real.exp (-cv * X) +
          (Real.exp (-alpha * X) + Real.exp (-beta * X))) ≤
      C * X / sMin + C * Real.exp (-c * X) := by
  dsimp only
  have halpha : 0 < Real.log (21 / 20 : ℝ) / 8 := by
    have : 0 < Real.log (21 / 20 : ℝ) :=
      Real.log_pos (by norm_num)
    positivity
  have hbeta : 0 < (7 / 64 : ℝ) := by norm_num
  have hc : 0 < min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) :=
    lt_min hcv (lt_min halpha hbeta)
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have hsMin0 : 0 ≤ sMin := le_trans (by norm_num) hsMin
  have hcommon0 : 0 ≤ Real.exp
      (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
    (Real.exp_pos _).le
  have hcvRate :
      min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) ≤ cv :=
    min_le_left _ _
  have halphaRate :
      min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) ≤
        Real.log (21 / 20 : ℝ) / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbetaRate :
      min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) ≤
        (7 / 64 : ℝ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hVexp :
      Real.exp (-cv * X) ≤ Real.exp
        (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hAexp :
      Real.exp (-(Real.log (21 / 20 : ℝ) / 8) * X) ≤ Real.exp
        (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hBexp :
      Real.exp (-(7 / 64 : ℝ) * X) ≤ Real.exp
        (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hExp :
      Kv * Real.exp (-cv * X) +
          (Real.exp (-(Real.log (21 / 20 : ℝ) / 8) * X) +
            Real.exp (-(7 / 64 : ℝ) * X)) ≤
        (Kv + 2) * Real.exp
          (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) := by
    have hVmul := mul_le_mul_of_nonneg_left hVexp hKv.le
    nlinarith
  have hCpoly : 0 < 270 * Kh / ch ^ 3 := by positivity
  have hquot : 0 ≤ X / sMin := div_nonneg hX0 hsMin0
  have hpoly :
      (270 * Kh / ch ^ 3) * (X / sMin) ≤
        max (270 * Kh / ch ^ 3) (Kv + 2) * (X / sMin) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hquot
  have hexpCoeff :
      (Kv + 2) * Real.exp
          (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) ≤
        max (270 * Kh / ch ^ 3) (Kv + 2) * Real.exp
          (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hcommon0
  calc
    270 * Kh / ch ^ 3 * X / sMin +
        (Kv * Real.exp (-cv * X) +
          (Real.exp (-(Real.log (21 / 20 : ℝ) / 8) * X) +
            Real.exp (-(7 / 64 : ℝ) * X))) =
        (270 * Kh / ch ^ 3) * (X / sMin) +
          (Kv * Real.exp (-cv * X) +
            (Real.exp (-(Real.log (21 / 20 : ℝ) / 8) * X) +
              Real.exp (-(7 / 64 : ℝ) * X))) := by ring
    _ ≤ max (270 * Kh / ch ^ 3) (Kv + 2) * (X / sMin) +
        (Kv + 2) * Real.exp
          (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
      add_le_add hpoly hExp
    _ ≤ max (270 * Kh / ch ^ 3) (Kv + 2) * (X / sMin) +
        max (270 * Kh / ch ^ 3) (Kv + 2) * Real.exp
          (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) :=
      add_le_add (le_refl _) hexpCoeff
    _ = max (270 * Kh / ch ^ 3) (Kv + 2) * X / sMin +
        max (270 * Kh / ch ^ 3) (Kv + 2) * Real.exp
          (-min cv (min (Real.log (21 / 20 : ℝ) / 8) (7 / 64 : ℝ)) * X) := by
      ring

/-- Large-branch form of Tao's `(7.61)` for the canonical endpoint/fresh
law.  The constants are uniform in the horizon, offset, entry point, and
source gap. -/
theorem lemma79CanonicalEndpointFreshEprimeAt_outerMeasure_le_largeBranch :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {J p Aweight fpGap : ℕ}
        {entry : TaoSection7RenewalPoint}
        {old : TaoSection7Triangle}
        {horizontalCenter sMin : ℝ},
        8 ≤ Aweight →
        p ≤ J →
        old.cornerL - entry.l = (fpGap : ℤ) →
        horizontalCenter = entry.toPoint.jReal + (fpGap : ℝ) / 4 →
        sMin ^ 2 ≤ 100 * (fpGap : ℝ) →
        30 * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)) ≤ sMin →
        (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
            (lemma79CanonicalEndpointFreshEprimeAt
              entry old horizontalCenter
              (2 * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)))
              (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)) p) ≤
          ENNReal.ofReal
            (C * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)) / sMin +
              C * Real.exp
                (-c * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)))) := by
  rcases lemma77CanonicalFirstPassageEndpointPMF_A_sq_mul_one_add_p_tail with
    ⟨Kv, cv, hKv, hcv, hVpre⟩
  rcases lemma77CanonicalFirstPassageHorizontalPMF_threeFifthsTail with
    ⟨Kh, ch, hKh, hch, hHpre⟩
  let alpha : ℝ := Real.log (21 / 20 : ℝ) / 8
  let beta : ℝ := 7 / 64
  let c : ℝ := min cv (min alpha beta)
  let Cpoly : ℝ := 270 * Kh / ch ^ 3
  let Cexp : ℝ := Kv + 2
  let C : ℝ := max Cpoly Cexp
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have : 0 < Real.log (21 / 20 : ℝ) :=
      Real.log_pos (by norm_num)
    positivity
  have hbeta : 0 < beta := by norm_num [beta]
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hcv (lt_min halpha hbeta)
  have hCpoly : 0 < Cpoly := by
    dsimp [Cpoly]
    positivity
  have hC : 0 ≤ C := by
    exact le_trans hCpoly.le (le_max_left _ _)
  refine ⟨C, c, hC, hc, ?_⟩
  intro J p Aweight fpGap entry old horizontalCenter sMin
    hAweight hpJ hgap hcenter hmaster hlarge
  let Xn : ℕ := Aweight ^ 2 * (p + 1)
  let X : ℝ := (Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)
  have hXcast : (Xn : ℝ) = X := by
    dsimp [Xn, X]
    push_cast
    ring
  have hAone : 1 ≤ Aweight := by omega
  have hX : 1 ≤ X := by
    have hAreal : (8 : ℝ) ≤ Aweight := by exact_mod_cast hAweight
    have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
    dsimp [X]
    nlinarith [sq_nonneg ((Aweight : ℝ) - 8)]
  have hsMin : 1 ≤ sMin := by
    nlinarith [hlarge, hX]
  have hgapNat : 1 ≤ fpGap := by
    by_contra hnot
    have hzero : fpGap = 0 := by omega
    subst fpGap
    norm_num at hmaster
    nlinarith [sq_nonneg sMin]
  have hthreeFifths :
      sMin / 16 ≤ (fpGap : ℝ) ^ (3 / 5 : ℝ) :=
    lemma79_sMin_div_sixteen_le_gap_threeFifths
      (Nat.cast_nonneg fpGap) hsMin hmaster
  have hVpreBound :
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
          (lemma77CanonicalVerticalOvershootTailEvent fpGap Xn) ≤
        ENNReal.ofReal (Kv * Real.exp (-cv * X)) := by
    simpa [Xn, X, Nat.add_comm] using
      hVpre entry fpGap Aweight p hAone
  have hVfreshBound :
      (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79CanonicalFreshVerticalTailEvent entry p Xn) ≤
        ENNReal.ofReal (Real.exp (-alpha * X)) := by
    simpa [Xn, X, alpha] using
      lemma79CanonicalFreshVerticalTailEvent_outerMeasure_le_alphaEighth
        p Aweight entry hAweight
  have hHpreBound :
      (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
          (lemma77CanonicalHorizontalDeviationEvent fpGap
            ((fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
        ENNReal.ofReal (Cpoly * X / sMin) := by
    calc
      _ ≤ ENNReal.ofReal
          (Kh * Real.exp (-ch * (fpGap : ℝ) ^ (1 / 5 : ℝ))) :=
        hHpre entry fpGap hgapNat
      _ ≤ ENNReal.ofReal (Cpoly * X / sMin) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [Cpoly] using
          (lemma79_threeFifthsTail_le_scale
            hKh hch hsMin hX hmaster)
  have hHfreshBound :
      (taoSection7HoldListPMF p).toOuterMeasure
          (lemma79CanonicalFreshHorizontalTailEvent p
            ((fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-beta * X)) := by
    simpa [X, beta] using
      lemma79CanonicalFreshHorizontalTailEvent_outerMeasure_le_sevenSixtyFour
        p Aweight fpGap sMin hAweight hlarge hthreeFifths
  have hfour :=
    lemma79CanonicalEndpointFreshEprimeAt_outerMeasure_le_fourMarginals
      (J := J) (p := p) (fpGap := fpGap) (X := Xn)
      (entry := entry) (old := old) (horizontalCenter := horizontalCenter)
      (t := (fpGap : ℝ) ^ (3 / 5 : ℝ)) hpJ hgap hcenter
  calc
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEprimeAt
          entry old horizontalCenter (2 * X)
          (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)) p) ≤
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
          (lemma77CanonicalVerticalOvershootTailEvent fpGap Xn) +
        ((taoSection7HoldListPMF p).toOuterMeasure
            (lemma79CanonicalFreshVerticalTailEvent entry p Xn) +
          ((lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
              (lemma77CanonicalHorizontalDeviationEvent fpGap
                ((fpGap : ℝ) ^ (3 / 5 : ℝ))) +
            (taoSection7HoldListPMF p).toOuterMeasure
              (lemma79CanonicalFreshHorizontalTailEvent p
                ((fpGap : ℝ) ^ (3 / 5 : ℝ))))) := by
      simpa [hXcast] using hfour
    _ ≤ ENNReal.ofReal (Kv * Real.exp (-cv * X)) +
        (ENNReal.ofReal (Real.exp (-alpha * X)) +
          (ENNReal.ofReal (Cpoly * X / sMin) +
            ENNReal.ofReal (Real.exp (-beta * X)))) := by
      gcongr
    _ = ENNReal.ofReal
        (Cpoly * X / sMin +
          (Kv * Real.exp (-cv * X) +
            (Real.exp (-alpha * X) + Real.exp (-beta * X)))) := by
      have hpoly0 : 0 ≤ Cpoly * X / sMin := by positivity
      have hV0 : 0 ≤ Kv * Real.exp (-cv * X) :=
        mul_nonneg hKv.le (Real.exp_pos _).le
      have hA0 : 0 ≤ Real.exp (-alpha * X) := (Real.exp_pos _).le
      have hB0 : 0 ≤ Real.exp (-beta * X) := (Real.exp_pos _).le
      rw [← ENNReal.ofReal_add hpoly0 hB0,
        ← ENNReal.ofReal_add hA0 (add_nonneg hpoly0 hB0),
        ← ENNReal.ofReal_add hV0
          (add_nonneg hA0 (add_nonneg hpoly0 hB0))]
      apply congrArg ENNReal.ofReal
      ring
    _ ≤ ENNReal.ofReal
        (C * X / sMin + C * Real.exp (-c * X)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa [alpha, beta, c, Cpoly, Cexp, C] using
        (lemma79_fourTailLargeBranch_scalar
          hKv hcv hKh hch hX hsMin)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
