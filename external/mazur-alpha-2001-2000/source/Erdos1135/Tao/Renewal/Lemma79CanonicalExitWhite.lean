import Erdos1135.Tao.Renewal.Prop78Case2Geometry

/-!
# Lemma 7.9 Canonical Localized Exit Whiteness

This proof leaf retains the strong strip information from the canonical
triangle family.  It shows that every supported endpoint in the canonical
localized first-passage window remains inside the source cutoff and is
cutoff-white.  The final theorem transfers the canonical one-half localized
mass bound to the corresponding white-endpoint event without conditioning or
finite sample-space assumptions.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A supported localized canonical exit stays inside the source cutoff.

The point is that the canonical family lies a full separation radius to the
left of the real cutoff.  The localized endpoint is closer than that radius to
an explicit point of its starting triangle.
-/
theorem lemma79CanonicalLocalizedEndpoint_sourceDomain
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {Delta : TaoSection7Triangle}
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    {start : TaoSection7RenewalPoint} {s r B : ℕ} {ell : ℤ}
    (hstart : Delta.Mem start.toPoint)
    (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ))
    (hlocalized : (r, ell) ∈ lemma77CanonicalLocalizedEndpointEvent s B)
    (hsupport : (s : ℤ) < ell)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation epsilon ^ 2) :
    taoSection7SourcePointInDomain (n / 2)
      (lemma77RenewalPointOfRelativeEndpoint start (r, ell)).toPoint := by
  let endpoint := lemma77RenewalPointOfRelativeEndpoint start (r, ell)
  rcases taoSection7Case2_exists_topRowWitness hstart hdepth
      hlocalized.1 hsupport hlocalized.2 with
    ⟨w, hw, _hOutside, hdist⟩
  let packet := taoSection7CanonicalFamilyPacket hxi hscalar
  have hwStrip :
      w.jReal ≤ taoSection7TriangleRightBound n epsilon :=
    packet.inStrip hDelta hw
  have hsep0 : 0 ≤ taoSection7TriangleSeparation epsilon :=
    zero_le_one.trans hscalar.separation_one
  have hdistSep :
      endpoint.toPoint.distSq w ≤ taoSection7TriangleSeparation epsilon ^ 2 :=
    hdist.le.trans hcollar
  have hcoord :=
    TaoSection7Point.abs_jReal_sub_le_of_distSq_le_sq
      endpoint.toPoint w hsep0 hdistSep
  have hdiff :
      endpoint.toPoint.jReal - w.jReal ≤
        taoSection7TriangleSeparation epsilon :=
    (le_abs_self _).trans hcoord
  have hhalf :
      endpoint.toPoint.jReal ≤ (n : ℝ) / 2 := by
    unfold taoSection7TriangleRightBound at hwStrip
    linarith
  have hdoubleReal :
      2 * (((endpoint.j : ℕ) : ℝ)) ≤ (n : ℝ) := by
    simpa [TaoSection7Point.jReal, TaoSection7RenewalPoint.toPoint] using
      (show 2 * endpoint.toPoint.jReal ≤ (n : ℝ) by linarith)
  have hdouble : 2 * (endpoint.j : ℕ) ≤ n := by
    exact_mod_cast hdoubleReal
  change (endpoint.j : ℕ) ≤ n / 2
  omega

/-- Every nonzero canonical endpoint atom in the localized window is
cutoff-white, with source-domain membership supplied by the canonical strip. -/
theorem lemma79CanonicalLocalizedEndpoint_sourceActualW
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {Delta : TaoSection7Triangle}
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    {start : TaoSection7RenewalPoint} {s r B : ℕ} {ell : ℤ}
    (hstart : Delta.Mem start.toPoint)
    (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ))
    (hlocalized : (r, ell) ∈ lemma77CanonicalLocalizedEndpointEvent s B)
    (hne : lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) ≠ 0)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation epsilon ^ 2) :
    taoSection7SourceActualW n xi epsilon
      (lemma77RenewalPointOfRelativeEndpoint start (r, ell)) := by
  have hsupport :=
    lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hne
  have hDomain := lemma79CanonicalLocalizedEndpoint_sourceDomain
    hxi hscalar hDelta hstart hdepth hlocalized hsupport.2 hcollar
  let hactive := TaoSection7Prop78ActiveCoverData.of_canonical hxi hscalar
  apply taoSection7SourceActualW_of_localizedEndpoint_activeCover
    hactive hDelta hstart hdepth hlocalized hsupport.2 hDomain hcollar

/-- The canonical localized half-mass transfers to actual cutoff-white exits.

Unsupported localized coordinates contribute zero PMF mass, so the raw
localized set need not be literally contained in the white event.
-/
theorem lemma79CanonicalFirstPassage_localizedExitWhite_mass_ge_half
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    {Delta : TaoSection7Triangle}
    (hDelta : Delta ∈ taoSection7CanonicalTriangleFamily hxi hscalar)
    {start : TaoSection7RenewalPoint} {s B : ℕ}
    (hstart : Delta.Mem start.toPoint)
    (hdepth : Delta.verticalDepth start.toPoint = (s : ℤ))
    (hlocalizedMass :
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s B)).toReal)
    (hcollar : taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation epsilon ^ 2) :
    (1 / 2 : ℝ) ≤
      ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        {x | taoSection7SourceActualW n xi epsilon
          (lemma77RenewalPointOfRelativeEndpoint start x)}).toReal := by
  classical
  let p := lemma77CanonicalFirstPassageEndpointPMF start s
  let localized := lemma77CanonicalLocalizedEndpointEvent s B
  let white : Set (ℕ × ℤ) :=
    {x | taoSection7SourceActualW n xi epsilon
      (lemma77RenewalPointOfRelativeEndpoint start x)}
  have hmass :
      p.toOuterMeasure localized ≤ p.toOuterMeasure white := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : x ∈ localized
    · by_cases hpx : p x = 0
      · simp [Set.indicator, hx, hpx]
      · have hxWhite : x ∈ white := by
          exact lemma79CanonicalLocalizedEndpoint_sourceActualW
            hxi hscalar hDelta hstart hdepth hx hpx hcollar
        simp [Set.indicator, hx, hxWhite]
    · simp [Set.indicator, hx]
  have huniv : p.toOuterMeasure Set.univ = 1 :=
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hfinite : p.toOuterMeasure white ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      p.toOuterMeasure white ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ white)
      _ = 1 := huniv
  have hmassReal :
      (p.toOuterMeasure localized).toReal ≤
        (p.toOuterMeasure white).toReal :=
    ENNReal.toReal_mono hfinite hmass
  exact hlocalizedMass.trans hmassReal

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
