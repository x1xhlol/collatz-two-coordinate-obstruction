import Erdos1135.Tao.Renewal.QEndpointFreshEprimeLargeBranch
import Erdos1135.Tao.Renewal.QEndpointFreshEprimeMasterWidth
import Erdos1135.Tao.Renewal.QEndpointFreshEStarEprime
import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeNative

/-!
# Canonical Fixed-Offset Lemma 7.10 Bound

This leaf combines the canonical `E'_p` estimate `(7.61)` with the canonical
outside-`E'_p` estimate `(7.62)`.  The small branch uses only total PMF mass;
the large branch uses the exact EStar/Eprime partition on the countable
endpoint/fresh carrier.

The theorem is the scheduled specialization at
`sMin = base^Kcut * (1+p)^3`; it does not claim Tao's broader
arbitrary-real-`s'` quantifier surface.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Source-uniform scheduled fixed-offset form of Lemma 7.10 for the
canonical endpoint/fresh law.  Constants are chosen before the offset cap
and its source-margin cutoff. -/
theorem lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_fixedOffset :
    ∃ constants : TaoSection7Lemma710Constants,
      ∀ (Aweight Pmax : ℕ), 8 ≤ Aweight →
        ∃ S0 : ℕ,
          ∀ (allowed : Finset ℕ)
            (n m J fpGap base Kcut p : ℕ)
            (entry : TaoSection7RenewalPoint)
            (family : Set TaoSection7Triangle)
            (old : TaoSection7Triangle) (M : ℝ),
            S0 ≤ fpGap →
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
                (constants.C710 * lemma79OutsideEprimeScale Aweight p /
                    taoSection7Case3LargeTriangleBoundWithBase
                      (base : ℝ) Kcut p +
                  constants.C710 * Real.exp
                    (-(constants.c710 *
                      lemma79OutsideEprimeScale Aweight p))) := by
  rcases
      lemma79CanonicalEndpointFreshEprimeAt_outerMeasure_le_largeBranch with
    ⟨C61, c61, hC61, hc61, h61⟩
  rcases
      lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_native
      with ⟨C762, hC762, h762⟩
  let constants : TaoSection7Lemma710Constants :=
    { C710 := 30 + C61 + C762
      c710 := c61
      C710_nonneg := by positivity
      c710_pos := hc61 }
  refine ⟨constants, ?_⟩
  intro Aweight Pmax hAweight
  have hAweightThree : 3 ≤ Aweight := by omega
  rcases h762 Aweight Pmax hAweightThree with ⟨S0, h762Rows⟩
  refine ⟨S0, ?_⟩
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
      dsimp [constants]
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
        h61 (J := J) (p := p) (Aweight := Aweight)
          (fpGap := fpGap) (entry := entry) (old := old)
          (horizontalCenter := entry.toPoint.jReal + (fpGap : ℝ) / 4)
          (sMin := sMin) hAweight hpJ hgap rfl hmaster hlargeRaw
      simpa [X, lemma79OutsideEprimeScale,
        lemma79OutsideEprimeScaleNat] using h
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
      simpa [mu, X, sMin] using h
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
        (by positivity) (mul_nonneg hC61 (Real.exp_pos _).le)
    have h762Real0 : 0 ≤ C762 * X / sMin := by positivity
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
          dsimp [constants]
          linarith
        have h61Coefficient : C61 ≤ constants.C710 := by
          dsimp [constants]
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
            dsimp [constants]
            ring

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
