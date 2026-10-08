import TrapOriginalStartTail
import Erdos1135.Tao.Renewal.Lemma79AllRBound
import Erdos1135.Tao.Renewal.CanonicalFirstPassageLocalizedMass

/-! Absolute renewal parameters and the actual original-start stopped-white bound. -/

set_option autoImplicit false

open CollatzResearch

namespace Erdos1135.Tao

open TaoSection7Lemma77
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

structure TrapRenewalParameters where
  L : ℕ
  epsilon : ℝ
  scalar : TaoSection7ClaimStarScalarPacket epsilon
  localizedMass : ∀ start s,
    (1 / 2 : ℝ) ≤
      ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalLocalizedEndpointEvent s L)).toReal
  collar : taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
    taoSection7TriangleSeparation epsilon ^ 2

theorem nonempty_trapRenewalParameters : Nonempty TrapRenewalParameters := by
  obtain ⟨L, _, hmass⟩ := lemma77CanonicalFirstPassageEndpointPMF_localized_absoluteMass
  let X : ℝ := taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2
  let E : ℝ := X + 1
  let epsilon : ℝ := Real.exp (-10 * E)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hE : 1 ≤ E := by dsimp [E]; linarith
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hepsilon10 : epsilon ≤ Real.exp (-10) := by
    dsimp [epsilon]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hscalar := TaoSection7ClaimStarScalarPacket.of_le_exp_neg_ten hepsilon hepsilon10
  have hinverse : 1 / epsilon = Real.exp (10 * E) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hseparation : taoSection7TriangleSeparation epsilon = E := by
    unfold taoSection7TriangleSeparation taoSection7TriangleLogScale
    rw [hinverse, Real.log_exp]
    ring
  refine ⟨⟨L, epsilon, hscalar, hmass, ?_⟩⟩
  rw [hseparation]
  change X ≤ E ^ 2
  dsimp [E]
  nlinarith [sq_nonneg X]

theorem trap_canonical_original_start_few_white_le
    (parameters : TrapRenewalParameters)
    (n J R T : ℕ) (xi : ZMod (3 ^ n)) (hxi : zmodThreePrimitive n xi) :
    trapPMFEvent (taoSection7HoldListPMF (n / 2 + 1))
        (trapOriginalStartFewWhiteEvent n (n / 2) J R T xi parameters.epsilon
          (taoSection7CanonicalTriangleFamily hxi parameters.scalar)) ≤
      Real.exp ((T : ℝ) + parameters.epsilon - parameters.epsilon * (R : ℝ)) := by
  apply trap_original_start_few_white_le_exp_of_native_moment
  intro start
  exact lemma79_canonical_all_R parameters.L parameters.localizedMass
    hxi parameters.scalar parameters.collar R start

end Erdos1135.Tao

#print axioms Erdos1135.Tao.nonempty_trapRenewalParameters
#print axioms Erdos1135.Tao.trap_canonical_original_start_few_white_le
