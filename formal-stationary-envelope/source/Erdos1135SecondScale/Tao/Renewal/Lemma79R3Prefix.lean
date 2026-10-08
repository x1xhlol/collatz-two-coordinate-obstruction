/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79PostExitFreshTail
import Erdos1135SecondScale.Tao.Renewal.Lemma79R2EndpointExpectation
import Erdos1135SecondScale.Tao.Renewal.Lemma79ClockDeath

/-!
# Lemma 7.9 Killed R=3 Prefix Contraction

This proof leaf transports the canonical two-valued endpoint contraction to
the stopped-prefix marginal used by the post-exit fresh-tail tower.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The stopped-prefix marginal has the same native two-valued endpoint
contraction as its canonical endpoint pushforward. -/
theorem lemma79_rawHoldFirstPassagePrefix_r2EndpointWeight_le_contraction
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {Delta : TaoSection7Triangle}
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    {entry : TaoSection7RenewalPoint} {gap L J : ℕ}
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
        (lemma79RawHoldFirstPassagePrefixPMF J entry gap)
        (fun pre =>
          lemma79R2EndpointWeight White
            (lemma77EndpointOfPrefix entry pre)) ≤
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
          White).toReal :=
    lemma79CanonicalFirstPassage_localizedExitWhite_mass_ge_half
      hxi hscalar hDelta hentry hdepth hlocalizedMass hcollar
  rw [lemma79_rawHoldFirstPassagePrefixPMF_eq_canonical]
  calc
    lemma79PMFENNExpectation
        (lemma77CanonicalFirstPassagePrefixPMF entry gap)
        (fun pre =>
          lemma79R2EndpointWeight White
            (lemma77EndpointOfPrefix entry pre)) =
        lemma79PMFENNExpectation
          (lemma77CanonicalFirstPassageEndpointPMF entry gap)
          (lemma79R2EndpointWeight White) := by
      unfold lemma77CanonicalFirstPassageEndpointPMF
      exact (lemma79PMFENNExpectation_map
        (lemma77CanonicalFirstPassagePrefixPMF entry gap)
        (lemma77EndpointOfPrefix entry)
        (lemma79R2EndpointWeight White)).symm
    _ ≤ ENNReal.ofReal lemma79R2ContractionFactor :=
      lemma79PMFENNExpectation_r2EndpointWeight_le_contraction
        (lemma77CanonicalFirstPassageEndpointPMF entry gap)
        White hwhiteMass

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
