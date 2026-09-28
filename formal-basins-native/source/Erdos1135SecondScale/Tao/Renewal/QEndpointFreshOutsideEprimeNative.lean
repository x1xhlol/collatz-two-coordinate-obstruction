/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeBudget

/-!
# Canonical Outside-Eprime Native Fixed-Offset Bound

This leaf assembles the exact-threshold small and large branches of Tao's
canonical complementary estimate `(7.62)`.  The kernel constant is global,
the offset cap and its row-margin cutoff are fixed before all sample
parameters, and the canonical carrier remains countable.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- One native constant covers the total-mass small branch and the explicit
horizontal-kernel large branch. -/
noncomputable def lemma79OutsideEprimeNativeConstant
    (C32 c32 : ℝ) : ℝ :=
  30 + lemma79OutsideEprimeMassConstant C32 c32

theorem lemma79OutsideEprimeNativeConstant_nonneg
    {C32 c32 : ℝ} (hC32 : 0 ≤ C32) (hc32 : 0 < c32) :
    0 ≤ lemma79OutsideEprimeNativeConstant C32 c32 := by
  unfold lemma79OutsideEprimeNativeConstant
  exact add_nonneg (by norm_num)
    (lemma79OutsideEprimeMassConstant_nonneg hC32 hc32)

/-- Any nonnegative coefficient below the native constant can be enlarged
inside the common `X / sMin` budget. -/
theorem lemma79OutsideEprimeCoefficient_le_native
    {C32 c32 coefficient X sMin : ℝ}
    (hcoefficient :
      coefficient ≤ lemma79OutsideEprimeNativeConstant C32 c32)
    (hX : 0 ≤ X) (hsMin : 0 ≤ sMin) :
    ENNReal.ofReal (coefficient * X / sMin) ≤
      ENNReal.ofReal
        (lemma79OutsideEprimeNativeConstant C32 c32 * X / sMin) := by
  apply ENNReal.ofReal_le_ofReal
  calc
    coefficient * X / sMin = coefficient * (X / sMin) := by ring
    _ ≤ lemma79OutsideEprimeNativeConstant C32 c32 * (X / sMin) :=
      mul_le_mul_of_nonneg_right hcoefficient (div_nonneg hX hsMin)
    _ = lemma79OutsideEprimeNativeConstant C32 c32 * X / sMin := by
      ring

/-- Exact fixed-offset canonical complementary estimate.  One
`AllowedCapAdmissibility` record controls both the row-margin cap and the
literal-threshold source widths. -/
theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_native :
    ∃ C762 : ℝ, 0 ≤ C762 ∧
      ∀ (Aweight Pmax : ℕ), 3 ≤ Aweight →
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
                (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
                  entry family old base Kcut p
                    (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                    (2 * lemma79OutsideEprimeScale Aweight p)
                    (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
              ENNReal.ofReal
                (C762 * lemma79OutsideEprimeScale Aweight p /
                  taoSection7Case3LargeTriangleBoundWithBase
                    (base : ℝ) Kcut p) := by
  rcases
      lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_explicit
    with ⟨C32, c32, hC32, hc32, hexplicit⟩
  refine
    ⟨lemma79OutsideEprimeNativeConstant C32 c32,
      lemma79OutsideEprimeNativeConstant_nonneg hC32 hc32, ?_⟩
  intro Aweight Pmax hAweight
  rcases
      exists_lemma79OutsideEprimeErrorMargin_cap_threshold
        Aweight Pmax with
    ⟨S0, hmarginCap⟩
  refine ⟨S0, ?_⟩
  intro allowed n m J fpGap base Kcut p entry family old M
    hS0 hpJ hgapAlign hbase hpair hold hscale hm hM hcap hpAllowed
  have hpPmax : p ≤ Pmax :=
    hcap.allowed_le_Pmax p hpAllowed
  have hschedule :
      TaoSection7Case3BaseKcutAdmissibilitySchedule
        allowed base m Kcut :=
    hcap.to_admissibilitySchedule
  let X : ℝ := lemma79OutsideEprimeScale Aweight p
  let sMin : ℝ :=
    taoSection7Case3LargeTriangleBoundWithBase
      (base : ℝ) Kcut p
  let R : ℕ := lemma79OutsideEprimeRadius Aweight p
  let mu := lemma79CanonicalEndpointFreshPMF J entry fpGap
  let Event :=
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
      entry family old base Kcut p
        (entry.toPoint.jReal + (fpGap : ℝ) / 4)
        (2 * X) (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))
  change
    mu.toOuterMeasure Event ≤
      ENNReal.ofReal
        (lemma79OutsideEprimeNativeConstant C32 c32 * X / sMin)
  have hadmissible :
      TaoSection7Case3EStarUsedOffsetAdmissible m p sMin := by
    simpa [sMin] using hschedule.admissible hpAllowed
  have hsMinOne : 1 ≤ sMin := hadmissible.2.1
  have hsMin0 : 0 ≤ sMin :=
    le_trans (by norm_num) hsMinOne
  have hsMinPos : 0 < sMin :=
    lt_of_lt_of_le (by norm_num) hsMinOne
  have hA2 : 9 ≤ Aweight ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hAweight hAweight
  have hXnat9 :
      9 ≤ lemma79OutsideEprimeScaleNat Aweight p := by
    apply hA2.trans
    dsimp [lemma79OutsideEprimeScaleNat]
    simpa using Nat.mul_le_mul_left (Aweight ^ 2)
      (show 1 ≤ p + 1 by omega)
  have hXnine : (9 : ℝ) ≤ X := by
    have hcast :
        (9 : ℝ) ≤
          (lemma79OutsideEprimeScaleNat Aweight p : ℝ) := by
      exact_mod_cast hXnat9
    simpa [X, lemma79OutsideEprimeScale] using hcast
  have hX0 : 0 ≤ X := le_trans (by norm_num) hXnine
  have hten : (10 : ℝ) ≤ 2 * X := by
    nlinarith
  have hCmass0 :
      0 ≤ lemma79OutsideEprimeMassConstant C32 c32 :=
    lemma79OutsideEprimeMassConstant_nonneg hC32 hc32
  have hthirty :
      (30 : ℝ) ≤ lemma79OutsideEprimeNativeConstant C32 c32 := by
    unfold lemma79OutsideEprimeNativeConstant
    linarith
  have hCmass :
      lemma79OutsideEprimeMassConstant C32 c32 ≤
        lemma79OutsideEprimeNativeConstant C32 c32 := by
    unfold lemma79OutsideEprimeNativeConstant
    linarith
  by_cases hsmall : sMin < 30 * X
  · have hmassSmall :
        mu.toOuterMeasure Event ≤
          ENNReal.ofReal (30 * X / sMin) :=
      lemma79PMFEvent_outerMeasure_le_smallBranch
        mu Event hsMinOne hsmall
    exact hmassSmall.trans
      (lemma79OutsideEprimeCoefficient_le_native
        hthirty hX0 hsMin0)
  · have hlarge : 30 * X ≤ sMin := le_of_not_gt hsmall
    have hscaleData :
        Lemma79OutsideEprimeLargeBranchScaleData
          Aweight p sMin := by
      apply lemma79OutsideEprimeLargeBranchScaleData_of_thirty_mul_le
        hAweight
      simpa [X] using hlarge
    have hwidth :
        (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) ∧
          (sigmaSeparationScale sMin) ^ 2 ≤
            1 + (fpGap : ℝ) := by
      have hwidthExact :=
        lemma79OutsideEprimeKernelWidths_of_baseKcutSchedule
          hscale hm hM hgapAlign hschedule hpAllowed
            (by simpa [R, sMin] using hscaleData.radius_le_tenth)
      simpa [R, sMin] using hwidthExact
    have hmargin :
        2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
            ((Real.log 2 / Real.log 9) * (2 * X) + 1) ≤
          (fpGap : ℝ) *
            (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
      simpa [X] using hmarginCap fpGap hS0 p hpPmax
    have hSAlign :
        (fpGap : ℝ) =
          ((old.cornerL - entry.toPoint.l : ℤ) : ℝ) := by
      have hcast :=
        congrArg (fun z : ℤ => (z : ℝ)) hgapAlign
      simpa [TaoSection7RenewalPoint.toPoint] using hcast.symm
    have hraw :
        mu.toOuterMeasure Event ≤
          ((2 * R + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal
              (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) := by
      have h :=
        hexplicit
          J fpGap base Kcut p R entry family old
          (entry.toPoint.jReal + (fpGap : ℝ) / 4)
          (2 * X)
          (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))
          sMin (fpGap : ℝ)
          (2 * X)
          (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))
          10 2 X (2 * X)
          hpJ hgapAlign hbase hSAlign rfl le_rfl le_rfl
          (by norm_num) (by positivity) (by positivity)
          hmargin hpair hold
          (by simp [sMin])
          hscaleData.sourceJ hscaleData.radius_absorbs
          hten le_rfl hscaleData.gap_absorbs
          hwidth.1 hscaleData.separation_ge_one hwidth.2
      simpa [mu, Event, R] using h
    have hcompressed :
        ((2 * R + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal
              (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) ≤
          ENNReal.ofReal
            (lemma79OutsideEprimeMassConstant C32 c32 * X / sMin) :=
      lemma79OutsideEprimeExplicitRHS_le_scale
        hC32 hc32 hsMinPos
        (by simpa [R, X] using hscaleData.window_card_le)
        hscaleData.floor_separation_lower
    exact (hraw.trans hcompressed).trans
      (lemma79OutsideEprimeCoefficient_le_native
        hCmass hX0 hsMin0)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
