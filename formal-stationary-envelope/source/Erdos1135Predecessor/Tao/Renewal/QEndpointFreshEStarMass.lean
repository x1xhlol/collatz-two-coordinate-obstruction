/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshSurvival

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open scoped BigOperators

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79CanonicalEndpointFreshEStarAt
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut p : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  {atom |
    taoSection7Case3LargeTriangleEvent
      (lemma79EndpointFreshPointAt entry atom) family p
      (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p)}

theorem lemma79CanonicalEndpointFreshEStarEvent_eq_biUnion_range
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut T R : ℕ) :
    lemma79CanonicalEndpointFreshEStarEvent entry family base Kcut T R =
      ⋃ p ∈ Finset.range
          (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1),
        lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p := by
  ext atom
  simp [lemma79CanonicalEndpointFreshEStarEvent,
    lemma79CanonicalEndpointFreshEStarAt,
    taoSection7Case3LargeTriangleEvent]

theorem lemma79CanonicalEndpointFreshEStarEvent_outerMeasure_le_sum
    (μ : PMF ((ℕ × ℤ) × List TaoSection7RenewalPoint))
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut T R : ℕ) :
    μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarEvent
          entry family base Kcut T R) ≤
      ∑ p ∈ Finset.range
          (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1),
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarAt
            entry family base Kcut p) := by
  rw [lemma79CanonicalEndpointFreshEStarEvent_eq_biUnion_range]
  exact MeasureTheory.measure_biUnion_finset_le _ _

theorem lemma79CanonicalEndpointFreshEStarEvent_toReal_le_sum
    (μ : PMF ((ℕ × ℤ) × List TaoSection7RenewalPoint))
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut T R : ℕ) :
    (μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarEvent
          entry family base Kcut T R)).toReal ≤
      ∑ p ∈ Finset.range
          (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1),
        (μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarAt
            entry family base Kcut p)).toReal := by
  have hnative :=
    lemma79CanonicalEndpointFreshEStarEvent_outerMeasure_le_sum
      μ entry family base Kcut T R
  have hsumTop :
      (∑ p ∈ Finset.range
          (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1),
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarAt
            entry family base Kcut p)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro p hp
    exact taoSection7PMFEventMass_ne_top μ _
  have hreal := ENNReal.toReal_mono hsumTop hnative
  rw [ENNReal.toReal_sum] at hreal
  · exact hreal
  · intro p hp
    exact taoSection7PMFEventMass_ne_top μ _

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
