import Erdos1135.Tao.Renewal.QEndpointFreshSurvival

/-!
# Canonical Endpoint/Fresh EStar Mass

This leaf isolates the countable-carrier finite-union algebra for the
canonical EStar event.  The fixed-offset probability estimate remains an
explicit downstream analytic obligation.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open scoped BigOperators
open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The fixed-offset slice of the canonical endpoint/fresh EStar event. -/
noncomputable def lemma79CanonicalEndpointFreshEStarAt
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut p : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  {atom |
    taoSection7Case3LargeTriangleEvent
      (lemma79EndpointFreshPointAt entry atom) family p
      (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p)}

/-- The full canonical EStar event is the inclusive finite union of its
fixed-offset slices through the sharp survival envelope. -/
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

/-- Native finite-union bound for the canonical EStar event.  This works on
the actual countable endpoint/fresh carrier and needs no `Fintype` instance. -/
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

/-- Safe real projection of the inclusive finite-union bound. -/
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
end Erdos1135
