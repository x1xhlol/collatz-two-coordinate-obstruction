/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEStarMass
import Erdos1135SecondScale.Tao.Renewal.Lemma79EndpointFreshLaw

/-!
# Canonical Endpoint/Fresh EStar Fibers

This leaf transfers a uniform event bound on every supported fresh-list fiber
to the actual countable independent endpoint/fresh carrier.  It is the native
Tonelli bridge needed before applying fixed-fresh horizontal-kernel estimates.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- A uniform event-mass bound on every supported right fiber transfers to an
independent PMF pair.  No countability or finite-carrier instance is needed. -/
theorem taoSection7PMFBindPair_eventMass_le_of_fiber
    {α β : Type*} (π : PMF α) (τ : PMF β)
    (Event : Set (α × β)) (B : ENNReal)
    (hfiber : ∀ b ∈ τ.support,
      π.toOuterMeasure {a | (a, b) ∈ Event} ≤ B) :
    (π.bind fun a => τ.map fun b => (a, b)).toOuterMeasure Event ≤ B := by
  have hcomm :
      π.bind (fun a => τ.map fun b => (a, b)) =
        τ.bind (fun b => π.map fun a => (a, b)) := by
    simpa only [PMF.map, Function.comp_apply] using
      (PMF.bind_comm π τ (fun a b => PMF.pure (a, b)))
  rw [hcomm, PMF.toOuterMeasure_bind_apply]
  calc
    (∑' b, τ b * (π.map fun a => (a, b)).toOuterMeasure Event) ≤
        ∑' b, τ b * B := by
      apply ENNReal.tsum_le_tsum
      intro b
      by_cases hb : b ∈ τ.support
      · apply mul_le_mul_right
        rw [PMF.toOuterMeasure_map_apply]
        exact hfiber b hb
      · have hτb : τ b = 0 := (τ.apply_eq_zero_iff b).2 hb
        simp [hτb]
    _ = B := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The endpoint section of a fixed-offset EStar slice after the fresh list is
fixed, written in explicit translated relative-endpoint coordinates. -/
noncomputable def lemma79CanonicalEndpointFreshEStarEndpointSection
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut p : ℕ) (fresh : List TaoSection7RenewalPoint) :
    Set (ℕ × ℤ) :=
  {endpoint |
    ∃ Delta : TaoSection7Triangle,
      Delta ∈ family ∧
      Delta.Mem
        (lemma77RenewalPointOfRelativeEndpoint entry
          (endpoint.1 + lemma77HoldPrefixHorizontalDelta p fresh,
            endpoint.2 +
              lemma77HoldPrefixVerticalIncrement entry p fresh)).toPoint ∧
      taoSection7Case3LargeTriangleBoundWithBase
          (base : ℝ) Kcut p ≤ Delta.size}

/-- Membership in a fixed EStar slice is exactly membership in its explicit
endpoint section after fixing the fresh list. -/
theorem lemma79CanonicalEndpointFreshEStarAt_mem_iff_endpointSection
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut p : ℕ) (endpoint : ℕ × ℤ)
    (fresh : List TaoSection7RenewalPoint) :
    (endpoint, fresh) ∈
        lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p ↔
      endpoint ∈ lemma79CanonicalEndpointFreshEStarEndpointSection
        entry family base Kcut p fresh := by
  simp only [lemma79CanonicalEndpointFreshEStarAt,
    taoSection7Case3LargeTriangleEvent, Set.mem_setOf_eq,
    lemma79CanonicalEndpointFreshEStarEndpointSection,
    lemma79EndpointFreshPointAt, lemma79EndpointFreshOrigin]
  rw [lemma79EndpointFresh_pathPoint_eq_relativeEndpoint]

/-- A uniform endpoint-fiber bound for a fixed canonical EStar offset lifts
to the complete endpoint/fresh PMF. -/
theorem lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_of_fresh_fibers
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ)
    (family : Set TaoSection7Triangle) (base Kcut p : ℕ) (B : ENNReal)
    (hfiber : ∀ fresh ∈ (taoSection7HoldListPMF J).support,
      (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure
          {endpoint |
            (endpoint, fresh) ∈
              lemma79CanonicalEndpointFreshEStarAt
                entry family base Kcut p} ≤ B) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarAt
          entry family base Kcut p) ≤ B := by
  exact taoSection7PMFBindPair_eventMass_le_of_fiber
    (lemma77CanonicalFirstPassageEndpointPMF entry gap)
    (taoSection7HoldListPMF J)
    (lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p)
    B hfiber

/-- A supported-fresh horizontal cover and a uniform horizontal-marginal mass
bound discharge the complete fixed-offset EStar slice.  Fresh randomness
enters only through the deterministic translated cover. -/
theorem
    lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_of_horizontal_fibers
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ)
    (family : Set TaoSection7Triangle) (base Kcut p : ℕ) (B : ENNReal)
    (horizontalEvent : List TaoSection7RenewalPoint → Set ℕ)
    (hcover : ∀ fresh ∈ (taoSection7HoldListPMF J).support,
      lemma79CanonicalEndpointFreshEStarEndpointSection
          entry family base Kcut p fresh ⊆
        {endpoint | endpoint.1 ∈ horizontalEvent fresh})
    (hbound : ∀ fresh ∈ (taoSection7HoldListPMF J).support,
      (lemma77CanonicalFirstPassageHorizontalPMF entry gap).toOuterMeasure
          (horizontalEvent fresh) ≤ B) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarAt
          entry family base Kcut p) ≤ B := by
  apply lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_of_fresh_fibers
  intro fresh hfresh
  calc
    (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure
        {endpoint |
          (endpoint, fresh) ∈
            lemma79CanonicalEndpointFreshEStarAt
              entry family base Kcut p} ≤
      (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure
        {endpoint | endpoint.1 ∈ horizontalEvent fresh} := by
          apply (lemma77CanonicalFirstPassageEndpointPMF
            entry gap).toOuterMeasure.mono
          intro endpoint hendpoint
          exact hcover fresh hfresh
            ((lemma79CanonicalEndpointFreshEStarAt_mem_iff_endpointSection
              entry family base Kcut p endpoint fresh).mp hendpoint)
    _ = (lemma77CanonicalFirstPassageHorizontalPMF entry gap).toOuterMeasure
        (horizontalEvent fresh) := by
          change
            (lemma77CanonicalFirstPassageEndpointPMF entry gap).toOuterMeasure
                (Prod.fst ⁻¹' horizontalEvent fresh) =
              ((lemma77CanonicalFirstPassageEndpointPMF entry gap).map
                Prod.fst).toOuterMeasure (horizontalEvent fresh)
          rw [PMF.toOuterMeasure_map_apply]
    _ ≤ B := hbound fresh hfresh

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end
end Tao
end Erdos1135SecondScale
