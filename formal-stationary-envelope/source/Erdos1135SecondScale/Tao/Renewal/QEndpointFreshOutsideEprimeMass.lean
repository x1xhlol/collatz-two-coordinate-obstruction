/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeHorizontal

/-!
# Canonical Outside-Eprime Joint Mass

This composition leaf combines support-aware canonical localization, the
fresh-fiber bind lift, and the uniform fixed-fresh horizontal estimate.  It is
the native countable-carrier outside-`E'_p` mass theorem; source-scale choices
and the separate exceptional-event estimate remain downstream.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Explicit canonical outside-`E'_p` mass bound.  The kernel constants are
chosen once, before any geometry or fresh-path parameter is quantified. -/
theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_explicit :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
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
              (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) := by
  rcases
      lemma79CanonicalFirstPassageHorizontalPMF_nearSigmaEvent_outerMeasure_le_explicit
    with ⟨C32, c32, hC32, hc32, hhorizontal⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
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

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
