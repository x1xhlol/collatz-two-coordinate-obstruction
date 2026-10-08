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

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageEndpoint
import Erdos1135Predecessor.Tao.Renewal.Lemma79AllRBound
import Erdos1135Predecessor.Tao.Renewal.Lemma79EndpointFreshCoordinates
import Erdos1135Predecessor.Tao.Renewal.Lemma79PostExitFreshTail

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79CanonicalEndpointFreshPMF
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (lemma77CanonicalFirstPassageEndpointPMF entry gap).bind fun endpoint =>
    (taoSection7HoldListPMF J).map fun fresh => (endpoint, fresh)

theorem lemma79CanonicalEndpointFreshPMF_apply
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ)
    (endpoint : ℕ × ℤ) (fresh : List TaoSection7RenewalPoint) :
    lemma79CanonicalEndpointFreshPMF J entry gap (endpoint, fresh) =
      lemma77CanonicalFirstPassageEndpointPMF entry gap endpoint *
        taoSection7HoldListPMF J fresh := by
  unfold lemma79CanonicalEndpointFreshPMF
  exact lemma79_prefixFreshTail_bind_apply
    (lemma77CanonicalFirstPassageEndpointPMF entry gap)
    (taoSection7HoldListPMF J) endpoint fresh

theorem lemma79CanonicalEndpointFreshPMF_nonzero_support
    {J : ℕ} {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {endpoint : ℕ × ℤ} {fresh : List TaoSection7RenewalPoint}
    (hne :
      lemma79CanonicalEndpointFreshPMF J entry gap (endpoint, fresh) ≠ 0) :
    0 < endpoint.1 ∧ (gap : ℤ) < endpoint.2 ∧ fresh.length = J := by
  rcases endpoint with ⟨r, ell⟩
  have hprod :
      lemma77CanonicalFirstPassageEndpointPMF entry gap (r, ell) *
          taoSection7HoldListPMF J fresh ≠ 0 := by
    rw [← lemma79CanonicalEndpointFreshPMF_apply]
    exact hne
  have hendpoint :
      lemma77CanonicalFirstPassageEndpointPMF entry gap (r, ell) ≠ 0 :=
    left_ne_zero_of_mul hprod
  have hfresh : taoSection7HoldListPMF J fresh ≠ 0 :=
    right_ne_zero_of_mul hprod
  have hendpointSupport :=
    lemma77CanonicalFirstPassageEndpointPMF_nonzero_support hendpoint
  have hlength : fresh.length = J := by
    by_contra hlength
    exact hfresh
      (taoSection7HoldListPMF_apply_eq_zero_of_length_ne J fresh hlength)
  exact ⟨hendpointSupport.1, hendpointSupport.2, hlength⟩

theorem lemma79CanonicalEndpointFreshPMF_horizontalAdvance_pos
    {J P : ℕ} {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {endpoint : ℕ × ℤ} {fresh : List TaoSection7RenewalPoint}
    (hne :
      lemma79CanonicalEndpointFreshPMF J entry gap (endpoint, fresh) ≠ 0) :
    0 < endpoint.1 + lemma77HoldPrefixHorizontalDelta P fresh :=
  Nat.add_pos_left
    (lemma79CanonicalEndpointFreshPMF_nonzero_support hne).1 _

theorem lemma79CanonicalEndpointFreshPMF_all_R
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (entry : TaoSection7RenewalPoint) (gap R : ℕ) :
    lemma79PMFENNExpectation
        (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap)
        (fun pair =>
          lemma79HoldPathCutoffTailMomentENN
            (lemma77RenewalPointOfRelativeEndpoint entry pair.1)
            (taoSection7CanonicalTriangleFamily hxi hscalar)
            n xi epsilon (n / 2) R pair.2) ≤
      ENNReal.ofReal (Real.exp epsilon) := by
  unfold lemma79CanonicalEndpointFreshPMF
  let C := ENNReal.ofReal (Real.exp epsilon)
  let future : (ℕ × ℤ) → List TaoSection7RenewalPoint → ENNReal :=
    fun endpoint fresh =>
      lemma79HoldPathCutoffTailMomentENN
        (lemma77RenewalPointOfRelativeEndpoint entry endpoint)
        (taoSection7CanonicalTriangleFamily hxi hscalar)
        n xi epsilon (n / 2) R fresh
  have htower := lemma79_pmfENNExpectation_bind_pair_prefix_mul_le
    (lemma77CanonicalFirstPassageEndpointPMF entry gap)
    (taoSection7HoldListPMF (n / 2))
    (fun _ => (1 : ENNReal)) future C
    (fun endpoint => by
      simpa [future, C] using
        (lemma79_canonical_all_R L hlocalizedMass hxi hscalar hcollar R
          (lemma77RenewalPointOfRelativeEndpoint entry endpoint)))
  have hconstant :
      lemma79PMFENNExpectation
          (lemma77CanonicalFirstPassageEndpointPMF entry gap)
          (fun _ => (1 : ENNReal) * C) ≤ C := by
    apply lemma79PMFENNExpectation_le_const
    intro endpoint
    simp
  exact (by simpa [future, C] using htower.trans hconstant)

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
