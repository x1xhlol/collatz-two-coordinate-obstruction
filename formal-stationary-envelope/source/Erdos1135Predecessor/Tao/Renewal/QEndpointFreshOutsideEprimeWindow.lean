/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageSigmaCenters
import Erdos1135Predecessor.Tao.Renewal.PMFIntWindowUnion
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeFiber

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open scoped BigOperators

open TaoSection7Lemma77

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem
    lemma79CanonicalFirstPassageHorizontalPMF_nearSigmaEvent_outerMeasure_le_windowBounds
    (entry : TaoSection7RenewalPoint) (fpGap p R : ℕ)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (sMin K B : ℝ) (fresh : List TaoSection7RenewalPoint)
    (centerBound : ℤ → ENNReal)
    (hpoint :
      ∀ c : sigmaHorizontalCenters family old sMin K B, ∀ r : ℕ,
        (r : ℤ) + lemma79EndpointFreshHorizontalShift entry p fresh ∈
            taoSection7IntIccWindow R c.1 →
          lemma77CanonicalFirstPassageHorizontalPMF entry fpGap r ≤
            centerBound c.1) :
    (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) ≤
      ((2 * R + 1 : ℕ) : ENNReal) *
        ∑' c : sigmaHorizontalCenters family old sMin K B,
          centerBound c.1 := by
  let shift := lemma79EndpointFreshHorizontalShift entry p fresh
  let coord : ℕ → ℤ := fun r => (r : ℤ) + shift
  have hcoord : Function.Injective coord := by
    intro r₁ r₂ h
    have hcast : (r₁ : ℤ) = (r₂ : ℤ) := by
      exact add_right_cancel h
    exact Int.ofNat_inj.mp hcast
  have hgeneric :=
    taoSection7PMF_intIccWindowUnion_outerMeasure_le
      (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap)
      coord hcoord (sigmaHorizontalCenters family old sMin K B)
      R centerBound
      (by
        intro c r hr
        exact hpoint c r (by simpa [coord, shift] using hr))
  have hevent :
      lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh =
        {r |
          ∃ c : sigmaHorizontalCenters family old sMin K B,
            coord r ∈ taoSection7IntIccWindow R c.1} := by
    ext r
    simp only [lemma79EndpointFreshNearSigmaHorizontalEvent,
      Set.mem_setOf_eq, sigmaHorizontalCenters]
    constructor
    · rintro ⟨q, hq, hr⟩
      refine ⟨⟨((q.j : ℕ) : ℤ), ⟨q, hq, rfl⟩⟩, ?_⟩
      simpa [coord, shift] using hr
    · rintro ⟨⟨c, q, hq, hc⟩, hr⟩
      subst c
      exact ⟨q, hq, by simpa [coord, shift] using hr⟩
  rw [hevent]
  exact hgeneric

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
