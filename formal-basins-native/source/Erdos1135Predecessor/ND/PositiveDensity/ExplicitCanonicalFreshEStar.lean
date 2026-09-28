/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalFreshEprime
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalOutsideEprime
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.HoldListVerticalTail
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarEprime
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeHorizontalTail
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeMarginalMass
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeMasterWidth
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeNative

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77 Tao.TaoSection7Lemma710

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

theorem explicitRenewal_freshEStar_fixedOffset :
    ∀ (Pmax : ℕ) (allowed : Finset ℕ)
            (n m J fpGap base Kcut p : ℕ)
            (entry : TaoSection7RenewalPoint)
            (family : Set TaoSection7Triangle)
            (old : TaoSection7Triangle) (M : ℝ),
            2 ^ 34 * (Pmax + 1) ≤ fpGap →
            p ≤ J →
            old.cornerL - entry.l = (fpGap : ℤ) →
            old.Mem entry.toPoint →
            TaoSection7TriangleFamilyPairwiseDisjoint family →
            old ∈ family →
            TaoSection7Lemma710CurrentScaleControls
              n old entry.toPoint M (fpGap : ℝ) →
            2 ≤ m →
            M = (m : ℝ) →
            TaoSection7Case3BaseKcutAllowedCapAdmissibility
              allowed base m Kcut Pmax →
            p ∈ allowed →
            (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
                (lemma79CanonicalEndpointFreshEStarAt
                  entry family base Kcut p) ≤
              ENNReal.ofReal
                (((2 : ℝ) ^ 116) * lemma79OutsideEprimeScale 8192 p /
                    taoSection7Case3LargeTriangleBoundWithBase
                      (base : ℝ) Kcut p +
                  ((2 : ℝ) ^ 116) * Real.exp
                    (-((1 / 256 : ℝ) *
                      lemma79OutsideEprimeScale 8192 p))) := by
  let C61 : ℝ := 2 ^ 112
  let c61 : ℝ := 1 / 256
  have hC61 : 0 ≤ C61 := by positivity
  have hc61 : 0 < c61 := by norm_num [c61]
  let C762 : ℝ := lemma79OutsideEprimeNativeConstant (2 ^ 21) (1 / 128)
  have hC762 : 0 ≤ C762 := lemma79OutsideEprimeNativeConstant_nonneg
    (by positivity) (by norm_num)
  have hC762bound := explicitRenewal_outsideEprime_constant_le
  let constants : TaoSection7Lemma710Constants :=
    { C710 := 2 ^ 116
      c710 := 1 / 256
      C710_nonneg := by positivity
      c710_pos := by norm_num }
  let Aweight : ℕ := 8192
  have hAweight : 8 ≤ Aweight := by norm_num [Aweight]
  intro Pmax
  have h762Rows := explicitRenewal_outsideEprime_native Pmax
  intro allowed n m J fpGap base Kcut p entry family old M
    hS0 hpJ hgap hbase hpair hold hscale hm hM hcap hpAllowed
  let X : ℝ := lemma79OutsideEprimeScale Aweight p
  let sMin : ℝ :=
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p
  let mu := lemma79CanonicalEndpointFreshPMF J entry fpGap
  let EStar :=
    lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p
  have hschedule :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        allowed base m Kcut :=
    hcap.to_admissibilitySchedule
  have hsMinOne : 1 ≤ sMin := by
    simpa [sMin] using (hschedule.admissible hpAllowed).2.1
  have hsMin0 : 0 ≤ sMin := le_trans (by norm_num) hsMinOne
  have hX0 : 0 ≤ X := by
    dsimp [X, lemma79OutsideEprimeScale,
      lemma79OutsideEprimeScaleNat]
    positivity
  have hquot0 : 0 ≤ X / sMin := div_nonneg hX0 hsMin0
  have hC710 : 0 ≤ constants.C710 := constants.C710_nonneg
  by_cases hsmall : sMin < 30 * X
  · have hmass :
        mu.toOuterMeasure EStar ≤
          ENNReal.ofReal (30 * X / sMin) :=
      lemma79PMFEvent_outerMeasure_le_smallBranch
        mu EStar hsMinOne hsmall
    apply hmass.trans
    apply ENNReal.ofReal_le_ofReal
    have hthirty : (30 : ℝ) ≤ constants.C710 := by
      dsimp [constants, C61, C762]
      linarith
    have hpoly :
        30 * (X / sMin) ≤ constants.C710 * (X / sMin) :=
      mul_le_mul_of_nonneg_right hthirty hquot0
    have hexpTerm :
        0 ≤ constants.C710 *
          Real.exp (-(constants.c710 * X)) :=
      mul_nonneg hC710 (Real.exp_pos _).le
    calc
      30 * X / sMin = 30 * (X / sMin) := by ring
      _ ≤ constants.C710 * (X / sMin) := hpoly
      _ ≤ constants.C710 * (X / sMin) +
          constants.C710 * Real.exp (-(constants.c710 * X)) :=
        le_add_of_nonneg_right hexpTerm
      _ = constants.C710 * X / sMin +
          constants.C710 * Real.exp (-(constants.c710 * X)) := by
        ring
  · have hlarge : 30 * X ≤ sMin := le_of_not_gt hsmall
    have hscaleM :
        TaoSection7Lemma710CurrentScaleControls
          n old entry.toPoint (m : ℝ) (fpGap : ℝ) := by
      simpa [hM] using hscale
    have hmaster : sMin ^ 2 ≤ 100 * (fpGap : ℝ) := by
      have hwidth :=
        lemma79EprimeMasterWidth_and_threeFifths_of_baseKcutSchedule
          hscaleM hschedule hpAllowed
      simpa [sMin] using hwidth.1
    have h61Bound :
        mu.toOuterMeasure
            (lemma79CanonicalEndpointFreshEprimeAt
              entry old
                (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)) p) ≤
          ENNReal.ofReal
            (C61 * X / sMin + C61 * Real.exp (-c61 * X)) := by
      have hlargeRaw :
          30 * ((Aweight : ℝ) ^ 2 * ((p : ℝ) + 1)) ≤ sMin := by
        simpa [X, lemma79OutsideEprimeScale,
          lemma79OutsideEprimeScaleNat] using hlarge
      have h :=
        explicitRenewal_freshEprime_largeBranch (J := J) (p := p) (Aweight := Aweight)
          (fpGap := fpGap) (entry := entry) (old := old)
          (horizontalCenter := entry.toPoint.jReal + (fpGap : ℝ) / 4)
          (sMin := sMin) hAweight hpJ hgap rfl hmaster hlargeRaw
      norm_num [mu, X, lemma79OutsideEprimeScale,
        lemma79OutsideEprimeScaleNat, C61, c61, Aweight] at h ⊢
      exact h
    have h762Bound :
        mu.toOuterMeasure
            (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
              entry family old base Kcut p
                (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
          ENNReal.ofReal (C762 * X / sMin) := by
      have h :=
        h762Rows allowed n m J fpGap base Kcut p entry family old M
          hS0 hpJ hgap hbase hpair hold hscale hm hM hcap hpAllowed
      simpa [mu, X, sMin, C762, Aweight] using h
    have hsplit :
        mu.toOuterMeasure EStar ≤
          mu.toOuterMeasure
              (lemma79CanonicalEndpointFreshEprimeAt
                entry old
                  (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                  (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)) p) +
            mu.toOuterMeasure
              (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
                entry family old base Kcut p
                  (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                  (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))) := by
      simpa [EStar] using
        (lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_eprime_add_outside
          mu entry family old base Kcut p
            (entry.toPoint.jReal + (fpGap : ℝ) / 4)
            (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)))
    have h61Real0 :
        0 ≤ C61 * X / sMin + C61 * Real.exp (-c61 * X) := by
      exact add_nonneg
        (div_nonneg (mul_nonneg hC61 hX0) hsMin0)
        (mul_nonneg hC61 (Real.exp_pos _).le)
    have h762Real0 : 0 ≤ C762 * X / sMin :=
      div_nonneg (mul_nonneg hC762 hX0) hsMin0
    calc
      mu.toOuterMeasure EStar ≤
          mu.toOuterMeasure
              (lemma79CanonicalEndpointFreshEprimeAt
                entry old
                  (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                  (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ)) p) +
            mu.toOuterMeasure
              (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
                entry family old base Kcut p
                  (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                  (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))) := hsplit
      _ ≤ ENNReal.ofReal
            (C61 * X / sMin + C61 * Real.exp (-c61 * X)) +
          ENNReal.ofReal (C762 * X / sMin) :=
        add_le_add h61Bound h762Bound
      _ = ENNReal.ofReal
          ((C61 * X / sMin + C61 * Real.exp (-c61 * X)) +
            C762 * X / sMin) :=
        (ENNReal.ofReal_add h61Real0 h762Real0).symm
      _ ≤ ENNReal.ofReal
          (constants.C710 * X / sMin +
            constants.C710 *
              Real.exp (-(constants.c710 * X))) := by
        apply ENNReal.ofReal_le_ofReal
        have hsumCoefficient : C61 + C762 ≤ constants.C710 := by
          dsimp [constants, C61, C762]
          linarith
        have h61Coefficient : C61 ≤ constants.C710 := by
          dsimp [constants, C61, C762]
          linarith
        have hpoly :
            (C61 + C762) * (X / sMin) ≤
              constants.C710 * (X / sMin) :=
          mul_le_mul_of_nonneg_right hsumCoefficient hquot0
        have hexp :
            C61 * Real.exp (-c61 * X) ≤
              constants.C710 * Real.exp (-c61 * X) :=
          mul_le_mul_of_nonneg_right h61Coefficient (Real.exp_pos _).le
        calc
          (C61 * X / sMin + C61 * Real.exp (-c61 * X)) +
              C762 * X / sMin =
            (C61 + C762) * (X / sMin) +
              C61 * Real.exp (-c61 * X) := by ring
          _ ≤ constants.C710 * (X / sMin) +
              constants.C710 * Real.exp (-c61 * X) :=
            add_le_add hpoly hexp
          _ = constants.C710 * X / sMin +
              constants.C710 *
                Real.exp (-(constants.c710 * X)) := by
            dsimp [constants, c61]
            ring

end

end Erdos1135Predecessor.ND.PositiveDensity
