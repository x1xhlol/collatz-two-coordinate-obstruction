/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.PMFExpectationThreeRegion
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeFourTail

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79CanonicalEprimeVerticalEndpointEvent_outerMeasure_eq
    (J : ℕ) (entry : TaoSection7RenewalPoint) (fpGap X : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEprimeVerticalEndpointEvent fpGap X) =
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma77CanonicalVerticalOvershootTailEvent fpGap X) := by
  change
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (Prod.fst ⁻¹'
          lemma77CanonicalVerticalOvershootTailEvent fpGap X) = _
  rw [← PMF.toOuterMeasure_map_apply,
    lemma79CanonicalEndpointFreshPMF_map_fst_eq]

theorem lemma79CanonicalEprimeFreshVerticalEvent_outerMeasure_eq
    {J p : ℕ} (hpJ : p ≤ J)
    (entry : TaoSection7RenewalPoint) (fpGap X : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEprimeFreshVerticalEvent entry p X) =
      (taoSection7HoldListPMF p).toOuterMeasure
        (lemma79CanonicalFreshVerticalTailEvent entry p X) := by
  change
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        ((fun atom :
            (ℕ × ℤ) × List TaoSection7RenewalPoint =>
              atom.2.take p) ⁻¹'
          lemma79CanonicalFreshVerticalTailEvent entry p X) = _
  rw [← PMF.toOuterMeasure_map_apply,
    lemma79CanonicalEndpointFreshPMF_map_fresh_take_eq_of_le
      (P := p) (J := J) hpJ entry fpGap]

theorem lemma79CanonicalEprimeHorizontalEndpointEvent_outerMeasure_eq
    (J : ℕ) (entry : TaoSection7RenewalPoint)
    (fpGap : ℕ) (t : ℝ) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEprimeHorizontalEndpointEvent fpGap t) =
      (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent fpGap t) := by
  change
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        ((fun atom :
            (ℕ × ℤ) × List TaoSection7RenewalPoint =>
              atom.1.1) ⁻¹'
          lemma77CanonicalHorizontalDeviationEvent fpGap t) = _
  rw [← PMF.toOuterMeasure_map_apply,
    lemma79CanonicalEndpointFreshPMF_map_horizontal_eq]

theorem lemma79CanonicalEprimeFreshHorizontalEvent_outerMeasure_eq
    {J p : ℕ} (hpJ : p ≤ J)
    (entry : TaoSection7RenewalPoint) (fpGap : ℕ) (t : ℝ) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEprimeFreshHorizontalEvent p t) =
      (taoSection7HoldListPMF p).toOuterMeasure
        (lemma79CanonicalFreshHorizontalTailEvent p t) := by
  change
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        ((fun atom :
            (ℕ × ℤ) × List TaoSection7RenewalPoint =>
              atom.2.take p) ⁻¹'
          lemma79CanonicalFreshHorizontalTailEvent p t) = _
  rw [← PMF.toOuterMeasure_map_apply,
    lemma79CanonicalEndpointFreshPMF_map_fresh_take_eq_of_le
      (P := p) (J := J) hpJ entry fpGap]

theorem lemma79CanonicalEndpointFreshEprimeAt_outerMeasure_le_fourMarginals
    {J p fpGap X : ℕ}
    {entry : TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {horizontalCenter t : ℝ}
    (hpJ : p ≤ J)
    (hgap : old.cornerL - entry.l = (fpGap : ℤ))
    (hcenter :
      horizontalCenter = entry.toPoint.jReal + (fpGap : ℝ) / 4) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEprimeAt
          entry old horizontalCenter (2 * (X : ℝ)) (2 * t) p) ≤
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
          (lemma77CanonicalVerticalOvershootTailEvent fpGap X) +
        ((taoSection7HoldListPMF p).toOuterMeasure
            (lemma79CanonicalFreshVerticalTailEvent entry p X) +
          ((lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
              (lemma77CanonicalHorizontalDeviationEvent fpGap t) +
            (taoSection7HoldListPMF p).toOuterMeasure
              (lemma79CanonicalFreshHorizontalTailEvent p t))) := by
  let mu := lemma79CanonicalEndpointFreshPMF J entry fpGap
  let Eprime :=
    lemma79CanonicalEndpointFreshEprimeAt
      entry old horizontalCenter (2 * (X : ℝ)) (2 * t) p
  let Vpre := lemma79CanonicalEprimeVerticalEndpointEvent fpGap X
  let Vfresh := lemma79CanonicalEprimeFreshVerticalEvent entry p X
  let Hpre := lemma79CanonicalEprimeHorizontalEndpointEvent fpGap t
  let Hfresh := lemma79CanonicalEprimeFreshHorizontalEvent p t
  have hcover :
      ∀ atom, mu atom ≠ 0 → atom ∈ Eprime →
        atom ∈ Vpre ∪ (Vfresh ∪ (Hpre ∪ Hfresh)) := by
    intro atom hne hmem
    exact
      lemma79CanonicalEndpointFreshEprimeAt_mem_fourTail_of_support
        hpJ hne hgap hcenter hmem
  calc
    mu.toOuterMeasure Eprime ≤
        mu.toOuterMeasure Vpre +
          mu.toOuterMeasure (Vfresh ∪ (Hpre ∪ Hfresh)) :=
      taoSection7PMFEventMass_le_add_of_support_cover mu hcover
    _ ≤ mu.toOuterMeasure Vpre +
        (mu.toOuterMeasure Vfresh +
          mu.toOuterMeasure (Hpre ∪ Hfresh)) :=
      by
        gcongr
        exact MeasureTheory.measure_union_le Vfresh (Hpre ∪ Hfresh)
    _ ≤ mu.toOuterMeasure Vpre +
        (mu.toOuterMeasure Vfresh +
          (mu.toOuterMeasure Hpre + mu.toOuterMeasure Hfresh)) :=
      by
        gcongr
        exact MeasureTheory.measure_union_le Hpre Hfresh
    _ =
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
          (lemma77CanonicalVerticalOvershootTailEvent fpGap X) +
        ((taoSection7HoldListPMF p).toOuterMeasure
            (lemma79CanonicalFreshVerticalTailEvent entry p X) +
          ((lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
              (lemma77CanonicalHorizontalDeviationEvent fpGap t) +
            (taoSection7HoldListPMF p).toOuterMeasure
              (lemma79CanonicalFreshHorizontalTailEvent p t))) := by
      rw [
        show mu.toOuterMeasure Vpre =
            (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
              (lemma77CanonicalVerticalOvershootTailEvent fpGap X) by
          simpa [mu, Vpre] using
            lemma79CanonicalEprimeVerticalEndpointEvent_outerMeasure_eq
              J entry fpGap X,
        show mu.toOuterMeasure Vfresh =
            (taoSection7HoldListPMF p).toOuterMeasure
              (lemma79CanonicalFreshVerticalTailEvent entry p X) by
          simpa [mu, Vfresh] using
            lemma79CanonicalEprimeFreshVerticalEvent_outerMeasure_eq
              hpJ entry fpGap X,
        show mu.toOuterMeasure Hpre =
            (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
              (lemma77CanonicalHorizontalDeviationEvent fpGap t) by
          simpa [mu, Hpre] using
            lemma79CanonicalEprimeHorizontalEndpointEvent_outerMeasure_eq
              J entry fpGap t,
        show mu.toOuterMeasure Hfresh =
            (taoSection7HoldListPMF p).toOuterMeasure
              (lemma79CanonicalFreshHorizontalTailEvent p t) by
          simpa [mu, Hfresh] using
            lemma79CanonicalEprimeFreshHorizontalEvent_outerMeasure_eq
              hpJ entry fpGap t]

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
