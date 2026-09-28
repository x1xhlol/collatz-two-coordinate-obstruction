/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79FirstEntryEndpointLaw
import Erdos1135SecondScale.Tao.Renewal.Lemma79CanonicalExitWhite
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2EndpointContraction
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2Aggregation
import Erdos1135SecondScale.Tao.Renewal.Lemma79FirstExit

/-!
# Lemma 7.9 First-Entry Endpoint Expectations

This proof leaf upgrades the canonical first-entry endpoint product law from
event masses to arbitrary native nonnegative endpoint weights.  Its final
theorem applies the canonical half-white estimate to the two-valued killed
`R=2` endpoint weight without conditioning or division by key mass.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Exact canonical endpoint expectation on one complete semantic first-entry
fiber inside an arbitrary longer Hold master. -/
theorem lemma79_holdList_firstEntryKey_canonicalEndpointExpectation
    {origin entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {C B p gap : ℕ}
    (hpC : p < C)
    (hroom : p + (gap + 1) ≤ B)
    (weight : (ℕ × ℤ) -> ENNReal) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey origin family C)
          (some (p, entry.toPoint))).indicator
            (fun full =>
              weight
                (lemma77CanonicalStoppedEndpoint entry gap
                  ((full.drop p).take (gap + 1))))) =
      (taoSection7HoldListPMF B).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey origin family C)
            (some (p, entry.toPoint))) *
        lemma79PMFENNExpectation
          (lemma77CanonicalFirstPassageEndpointPMF entry gap) weight := by
  let future : List TaoSection7RenewalPoint -> ENNReal :=
    fun tail => weight (lemma77CanonicalStoppedEndpoint entry gap tail)
  have hfactor :=
    lemma79_holdList_firstEntryKey_freshBlockExpectation_of_add_le
      (start := origin) (family := family) (C := C)
      (p := p) (N := gap + 1) (B := B)
      (entry := entry.toPoint) hpC hroom future
  have hkeyMass :=
    lemma79_holdList_firstEntryKey_mass_eq_prefixMass_of_add_le
      (start := origin) (family := family) (C := C)
      (p := p) (N := gap + 1) (B := B)
      (entry := entry.toPoint) hpC hroom
  have hendpoint :
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (gap + 1)) future =
        lemma79PMFENNExpectation
          (lemma77CanonicalFirstPassageEndpointPMF entry gap) weight := by
    calc
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF (gap + 1)) future =
          lemma79PMFENNExpectation
            ((taoSection7HoldListPMF (gap + 1)).map
              (lemma77CanonicalStoppedEndpoint entry gap)) weight :=
        (lemma79PMFENNExpectation_map
          (taoSection7HoldListPMF (gap + 1))
          (lemma77CanonicalStoppedEndpoint entry gap) weight).symm
      _ = _ := by
        rw [← lemma77CanonicalFirstPassageEndpointPMF_eq_holdList_map]
  rw [← hkeyMass, hendpoint] at hfactor
  simpa [future, lemma79KeyAtom, lemma79HoldPathHeadKey] using hfactor

/-- On one canonical first-entry key, the native two-valued endpoint weight is
bounded by the unnormalized key mass times the killed `R=2` contraction
factor. -/
theorem lemma79_holdList_firstEntryKey_r2EndpointWeight_le_contraction
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {Delta : TaoSection7Triangle}
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    {origin entry : TaoSection7RenewalPoint}
    {C B p gap L : ℕ}
    (hpC : p < C)
    (hroom : p + (gap + 1) ≤ B)
    (hentry : Delta.Mem entry.toPoint)
    (hgap : lemma79EntryVerticalGap Delta entry.toPoint = gap)
    (hlocalizedMass :
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent gap L)).toReal)
    (hcollar : taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation epsilon ^ 2) :
    let White : Set (ℕ × ℤ) :=
      {x | taoSection7SourceActualW n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint entry x)}
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey origin
            (taoSection7CanonicalTriangleFamily hxi hscalar) C)
          (some (p, entry.toPoint))).indicator
            (fun full =>
              lemma79R2EndpointWeight White
                (lemma77CanonicalStoppedEndpoint entry gap
                  ((full.drop p).take (gap + 1))))) ≤
      (taoSection7HoldListPMF B).toOuterMeasure
          (lemma79KeyAtom Set.univ
            (lemma79HoldPathHeadKey origin
              (taoSection7CanonicalTriangleFamily hxi hscalar) C)
            (some (p, entry.toPoint))) *
        ENNReal.ofReal lemma79R2ContractionFactor := by
  dsimp only
  let White : Set (ℕ × ℤ) :=
    {x | taoSection7SourceActualW n xi epsilon
      (lemma77RenewalPointOfRelativeEndpoint entry x)}
  have hdepth : Delta.verticalDepth entry.toPoint = (gap : ℤ) := by
    rw [← hgap]
    exact lemma79EntryVerticalGap_coe_of_mem hentry
  have hwhiteMass :
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure
          White).toReal := by
    exact lemma79CanonicalFirstPassage_localizedExitWhite_mass_ge_half
      hxi hscalar hDelta hentry hdepth hlocalizedMass hcollar
  rw [lemma79_holdList_firstEntryKey_canonicalEndpointExpectation
    (family := taoSection7CanonicalTriangleFamily hxi hscalar)
    hpC hroom (lemma79R2EndpointWeight White)]
  gcongr
  exact lemma79PMFENNExpectation_r2EndpointWeight_le_contraction
    (lemma77CanonicalFirstPassageEndpointPMF entry gap) White hwhiteMass

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
