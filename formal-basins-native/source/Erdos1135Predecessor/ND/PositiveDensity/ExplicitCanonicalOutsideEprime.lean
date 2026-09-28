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
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalSourceMargin
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeNative

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77 Tao.TaoSection7Lemma710

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

open scoped BigOperators

noncomputable section

theorem
    explicitRenewal_nearSigma_bound :
      ∀ (entry : TaoSection7RenewalPoint) (fpGap p R : ℕ)
        (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
        (sMin K B : ℝ) (fresh : List TaoSection7RenewalPoint),
        TaoSection7TriangleFamilyPairwiseDisjoint family →
        TaoSection7Triangle.lemma710GapAbsorbs K B sMin →
        (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) →
        1 ≤ sigmaSeparationScale sMin →
        (sigmaSeparationScale sMin) ^ 2 ≤ 1 + (fpGap : ℝ) →
        (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
            (lemma79EndpointFreshNearSigmaHorizontalEvent
              entry family old sMin K B p R fresh) ≤
          ((2 * R + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal
              (lemma79NearSigmaHorizontalCenterMassBound (2 ^ 21) (1 / 128) sMin) := by
  let C32 : ℝ := 2 ^ 21
  let c32 : ℝ := 1 / 128
  have hC32 : 0 ≤ C32 := by positivity
  have hc32 : 0 < c32 := by norm_num [c32]
  have hcanonical := explicitRenewal_horizontalPMF_le
  intro entry fpGap p R family old sMin K B fresh
    hpair habsorb hRwidth hscale hsepwidth
  let shift := lemma79EndpointFreshHorizontalShift entry p fresh
  let amplitude : ℝ := 2 * Real.exp (c32 ^ 2)
  let kernel : ℤ → ℝ := fun z =>
    lemma77SignedTranslatedHorizontalKernel
      (300 * C32) (c32 / 2) shift fpGap z
  let centerBound : ℤ → ENNReal := fun z =>
    ENNReal.ofReal (amplitude * kernel z)
  let sparseBound : ℝ :=
    (2 * Real.exp ((c32 / 2) ^ 2) /
        (Nat.floor (sigmaSeparationScale sMin) : ℝ)) *
      ((300 * C32) *
        (lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) +
          lemma77HorizontalLinearCountConstant (c32 / 4)))
  have hC300 : 0 ≤ 300 * C32 :=
    mul_nonneg (by norm_num) hC32
  have hAmplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    positivity
  have hkernel0 (z : ℤ) : 0 ≤ kernel z := by
    exact lemma77SignedTranslatedHorizontalKernel_nonneg
      hC300 shift fpGap z
  have hkernelSummable :
      Summable fun c : sigmaHorizontalCenters family old sMin K B =>
        kernel c.1 := by
    simpa only [kernel, Function.comp_apply] using
      (lemma77SignedTranslatedHorizontalKernel_summable
        (C := 300 * C32) (r := c32 / 2)
        (half_pos hc32) shift fpGap).comp_injective
          Subtype.val_injective
  have hcenterSummable :
      Summable fun c : sigmaHorizontalCenters family old sMin K B =>
        amplitude * kernel c.1 :=
    hkernelSummable.mul_left amplitude
  have hcenter0 :
      ∀ c : sigmaHorizontalCenters family old sMin K B,
        0 ≤ amplitude * kernel c.1 :=
    fun c => mul_nonneg hAmplitude (hkernel0 c.1)
  have hcenterReal :
      (∑' c : sigmaHorizontalCenters family old sMin K B,
        kernel c.1) ≤ sparseBound := by
    have hsparse :=
      lemma77SignedTranslatedHorizontalKernel_tsum_sigma_le
        (old := old) hpair habsorb hC300 hc32 shift fpGap hscale hsepwidth
    rw [tsum_sigma_eq_tsum_horizontalCenters] at hsparse
    simpa only [kernel, sparseBound] using hsparse
  have hcenterENNReal :
      (∑' c : sigmaHorizontalCenters family old sMin K B,
        centerBound c.1) ≤
          ENNReal.ofReal (amplitude * sparseBound) := by
    change
      (∑' c : sigmaHorizontalCenters family old sMin K B,
        ENNReal.ofReal (amplitude * kernel c.1)) ≤
          ENNReal.ofReal (amplitude * sparseBound)
    rw [← ENNReal.ofReal_tsum_of_nonneg hcenter0 hcenterSummable]
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hcenterReal hAmplitude
  have hwindow :=
    lemma79CanonicalFirstPassageHorizontalPMF_nearSigmaEvent_outerMeasure_le_windowBounds
      entry fpGap p R family old sMin K B fresh centerBound
      (by
        intro center r hr
        exact
          lemma79CanonicalFirstPassageHorizontalPMF_windowAtom_le_signedCenter
            hC32 hc32 hcanonical entry fpGap R shift center.1 r
              hRwidth (by simpa [shift] using hr))
  calc
    (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) ≤
      ((2 * R + 1 : ℕ) : ENNReal) *
        ∑' c : sigmaHorizontalCenters family old sMin K B,
          centerBound c.1 := hwindow
    _ ≤ ((2 * R + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal (amplitude * sparseBound) :=
      by gcongr
    _ = ((2 * R + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal
          (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) := by
      simp only [lemma79NearSigmaHorizontalCenterMassBound,
        amplitude, sparseBound]

theorem
    explicitRenewal_outsideEprime_raw :
      ∀ (J fpGap base Kcut p R : ℕ)
        (entry : TaoSection7RenewalPoint)
        (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
        (horizontalCenter verticalSourceThreshold horizontalSourceThreshold
          sMin S Lerr Jerr gap geomK geomB Jgeo : ℝ),
        p ≤ J →
        old.cornerL - entry.l = (fpGap : ℤ) →
        old.Mem entry.toPoint →
        S = ((old.cornerL - entry.toPoint.l : ℤ) : ℝ) →
        horizontalCenter = entry.toPoint.jReal + S / 4 →
        verticalSourceThreshold ≤ Lerr →
        horizontalSourceThreshold ≤ Jerr →
        0 ≤ gap →
        0 ≤ Lerr →
        0 ≤ Jerr →
        Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
          S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) →
        TaoSection7TriangleFamilyPairwiseDisjoint family →
        old ∈ family →
        sMin ≤ taoSection7Case3LargeTriangleBoundWithBase
          (base : ℝ) Kcut p →
        (Real.log 2 / Real.log 9) *
            (geomK * geomB + geomK * geomB) ≤ Jgeo →
        Jgeo ^ 2 + (geomK * geomB) ^ 2 ≤ (R : ℝ) ^ 2 →
        gap ≤ geomK * geomB →
        Lerr ≤ geomK * geomB →
        TaoSection7Triangle.lemma710GapAbsorbs geomK geomB sMin →
        (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) →
        1 ≤ sigmaSeparationScale sMin →
        (sigmaSeparationScale sMin) ^ 2 ≤ 1 + (fpGap : ℝ) →
        (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
            (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
              entry family old base Kcut p horizontalCenter
                verticalSourceThreshold horizontalSourceThreshold) ≤
          ((2 * R + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal
              (lemma79NearSigmaHorizontalCenterMassBound (2 ^ 21) (1 / 128) sMin) := by
  let C32 : ℝ := 2 ^ 21
  let c32 : ℝ := 1 / 128
  have hhorizontal := explicitRenewal_nearSigma_bound
  intro J fpGap base Kcut p R entry family old horizontalCenter
    verticalSourceThreshold horizontalSourceThreshold sMin S Lerr Jerr gap
    geomK geomB Jgeo hpJ hgapAlign hbase hS hcenter hV hJerr hgap0 hL0
    hJ0 hmargin hpair hold hsize hJgeo hradius hgapKB hLerrKB habsorb
    hRwidth hscale hsepwidth
  exact
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_of_horizontalEvents
      (J := J) (fpGap := fpGap) (base := base) (Kcut := Kcut)
      (p := p) (R := R) (entry := entry) (family := family) (old := old)
      (horizontalCenter := horizontalCenter)
      (verticalSourceThreshold := verticalSourceThreshold)
      (horizontalSourceThreshold := horizontalSourceThreshold)
      (sMin := sMin) (S := S) (Lerr := Lerr) (Jerr := Jerr)
      (gap := gap) (K := geomK) (B := geomB) (Jgeo := Jgeo)
      (Bbound := ((2 * R + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal
          (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin))
      hpJ hgapAlign hbase hS hcenter hV hJerr hgap0 hL0 hJ0 hmargin
      hpair hold hsize hJgeo hradius hgapKB hLerrKB
      (fun fresh _ =>
        hhorizontal entry fpGap p R family old sMin geomK geomB fresh
          hpair habsorb hRwidth hscale hsepwidth)

theorem explicitRenewal_outsideEprime_constant_le :
    lemma79OutsideEprimeNativeConstant (2 ^ 21) (1 / 128) ≤ (2 : ℝ) ^ 68 := by
  have h1 : Real.exp ((1 / 128 : ℝ) ^ 2) ≤ 2 := by
    exact (Real.exp_bound_div_one_sub_of_interval (by positivity) (by norm_num)).trans
      (by norm_num)
  have h2 : Real.exp (((1 / 128 : ℝ) / 2) ^ 2) ≤ 2 := by
    exact (Real.exp_bound_div_one_sub_of_interval (by positivity) (by norm_num)).trans
      (by norm_num)
  have h12 : Real.exp ((1 / 128 : ℝ) ^ 2) * Real.exp (((1 / 128 : ℝ) / 2) ^ 2) ≤ 4 := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2)
  have hG : lemma77HorizontalGaussianCountConstant (((1 / 128 : ℝ) / 4) ^ 2) ≤ 2 ^ 24 := by
    have h := explicitRenewal_gaussianCount_le
      (by norm_num : (0 : ℝ) < ((1 / 128 : ℝ) / 4) ^ 2) (by norm_num)
    norm_num at h ⊢
    exact h
  have hL : lemma77HorizontalLinearCountConstant ((1 / 128 : ℝ) / 4) ≤ 2 ^ 13 := by
    have h := explicitRenewal_linearCount_le (by norm_num : (0 : ℝ) < (1 / 128 : ℝ) / 4)
      (by norm_num)
    norm_num at h ⊢
    exact h
  have hGL0 : 0 ≤ lemma77HorizontalGaussianCountConstant (((1 / 128 : ℝ) / 4) ^ 2) +
      lemma77HorizontalLinearCountConstant ((1 / 128 : ℝ) / 4) :=
    add_nonneg (lemma77HorizontalGaussianCountConstant_nonneg (by norm_num))
      (lemma77HorizontalLinearCountConstant_nonneg (by norm_num))
  have hprod := mul_le_mul h12 (add_le_add hG hL) hGL0 (by norm_num : (0 : ℝ) ≤ 4)
  unfold lemma79OutsideEprimeNativeConstant lemma79OutsideEprimeMassConstant
  norm_num only at hprod ⊢
  nlinarith only [hprod]

theorem explicitRenewal_outsideEprime_native :
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
                (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
                  entry family old base Kcut p
                    (entry.toPoint.jReal + (fpGap : ℝ) / 4)
                    (2 * lemma79OutsideEprimeScale 8192 p)
                    (2 * (fpGap : ℝ) ^ (3 / 5 : ℝ))) ≤
              ENNReal.ofReal
                (lemma79OutsideEprimeNativeConstant (2 ^ 21) (1 / 128) * lemma79OutsideEprimeScale 8192 p /
                  taoSection7Case3LargeTriangleBoundWithBase
                    (base : ℝ) Kcut p) := by
  let C32 : ℝ := 2 ^ 21
  let c32 : ℝ := 1 / 128
  have hC32 : 0 ≤ C32 := by positivity
  have hc32 : 0 < c32 := by norm_num [c32]
  have hexplicit := explicitRenewal_outsideEprime_raw
  let Aweight : ℕ := 8192
  have hAweight : 3 ≤ Aweight := by norm_num [Aweight]
  intro Pmax
  have hmarginCap : ∀ fpGap : ℕ, 2 ^ 34 * (Pmax + 1) ≤ fpGap →
      ∀ p : ℕ, p ≤ Pmax →
      2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) * (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
          (fpGap : ℝ) * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
    intro fpGap hS p hp
    exact explicitRenewal_sourceMargin hS hp
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
      simpa [mu, Event, R, C32, c32] using h
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

end

end Erdos1135Predecessor.ND.PositiveDensity
