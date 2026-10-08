/- This local copy changes proof tactics only to satisfy the pinned toolchain linters.
   The theorem statements are unchanged; see provenance/native-linter-patches.json. -/

import Erdos1135.Tao.Renewal.CanonicalFirstPassageEndpoint
import Erdos1135.Tao.Renewal.Lemma79AllRBound
import Erdos1135.Tao.Renewal.Lemma79EndpointFreshCoordinates
import Erdos1135.Tao.Renewal.Lemma79PostExitFreshTail

/-!
# Lemma 7.9 Endpoint/Fresh-Tail Law

This proof leaf pushes the canonical stopped-prefix/fresh-tail split to the
relative first-passage endpoint.  The endpoint remains relative to the entry
point; later consumers apply `lemma77RenewalPointOfRelativeEndpoint` when an
absolute restart origin is required.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The active countable Case 3 carrier: a relative canonical first-passage
endpoint followed by an independent fresh length-`J` Hold block. -/
noncomputable def lemma79CanonicalEndpointFreshPMF
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (lemma77CanonicalFirstPassageEndpointPMF entry gap).bind fun endpoint =>
    (taoSection7HoldListPMF J).map fun fresh => (endpoint, fresh)

/-- Every atom of the endpoint/fresh carrier factors into its endpoint and
fresh-Hold marginals. -/
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

/-- A nonzero endpoint/fresh atom has a valid canonical endpoint and a fresh
list of exactly the carrier horizon. -/
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

/-- Every supported endpoint/fresh atom has strictly positive total horizontal
advance, independently of the consumed fresh horizon. -/
theorem lemma79CanonicalEndpointFreshPMF_horizontalAdvance_pos
    {J P : ℕ} {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {endpoint : ℕ × ℤ} {fresh : List TaoSection7RenewalPoint}
    (hne :
      lemma79CanonicalEndpointFreshPMF J entry gap (endpoint, fresh) ≠ 0) :
    0 < endpoint.1 + lemma77HoldPrefixHorizontalDelta P fresh :=
  Nat.add_pos_left
    (lemma79CanonicalEndpointFreshPMF_nonzero_support hne).1 _

/-- Pushing the raw stopped-prefix/fresh-tail split to its relative endpoint
gives the canonical endpoint/fresh carrier exactly. -/
theorem lemma79_rawHoldFirstPassageFixedTailSplitPMF_map_endpoint_fresh
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF
        (gap + 1 + J) J entry gap).map
      (fun pair => (lemma77EndpointOfPrefix entry pair.1, pair.2)) =
      lemma79CanonicalEndpointFreshPMF J entry gap := by
  rw [lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind]
  rw [lemma79_rawHoldFirstPassagePrefixPMF_eq_canonical]
  unfold lemma79CanonicalEndpointFreshPMF
  unfold lemma77CanonicalFirstPassageEndpointPMF
  rw [PMF.map_bind, PMF.bind_map]
  congr
  funext stopped
  rw [PMF.map_comp]
  apply congrArg (fun f => (taoSection7HoldListPMF J).map f)
  funext fresh
  rfl

/-- The canonical killed all-`R` moment bound integrates over the endpoint
marginal of the same endpoint/fresh carrier.  Only the integrand converts the
relative endpoint to its absolute restart origin. -/
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
end Erdos1135
