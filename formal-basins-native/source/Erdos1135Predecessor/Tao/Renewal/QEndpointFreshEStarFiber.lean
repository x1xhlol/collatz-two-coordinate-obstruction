/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79EndpointFreshLaw
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarMass

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
