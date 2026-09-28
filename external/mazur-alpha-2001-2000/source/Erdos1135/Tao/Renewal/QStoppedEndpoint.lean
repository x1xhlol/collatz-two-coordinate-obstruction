import Erdos1135.Tao.Renewal.CanonicalFirstPassageEndpoint
import Erdos1135.Tao.Renewal.QStoppedApprox

/-!
# Stopped Q Endpoint Pushforward

This leaf discards the endpoint-exclusive stopped-prefix factor while the
expectation is still indexed by prefixes.  Only the remaining endpoint-valued
payload is then transported through the canonical endpoint PMF.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- Drop the stopped-prefix factor before pushing an endpoint-valued payload
through the canonical endpoint map.  No endpoint measurability of the prefix
factor is asserted. -/
theorem taoSection7CanonicalFirstPassagePrefixFactor_endpointPayload_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (F : ℕ × ℤ → ℝ)
    (hF0 : ∀ x, 0 ≤ F x)
    (hF1 : ∀ x, F x ≤ 1) :
    (∑' pre : List TaoSection7RenewalPoint,
      (lemma77CanonicalFirstPassagePrefixPMF start gap pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre *
          F (lemma77EndpointOfPrefix start pre))) ≤
      ∑' x : ℕ × ℤ,
        (lemma77CanonicalFirstPassageEndpointPMF start gap x).toReal * F x := by
  let p := lemma77CanonicalFirstPassagePrefixPMF start gap
  let f := lemma77EndpointOfPrefix start
  have htransport := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    p f F hF0 hF1
  have hright : Summable fun pre : List TaoSection7RenewalPoint =>
      (p pre).toReal * F (f pre) := htransport.2.1
  have hpoint : ∀ pre : List TaoSection7RenewalPoint,
      (p pre).toReal *
          (taoSection7QPrefixFactor epsilon W start pre * F (f pre)) ≤
        (p pre).toReal * F (f pre) := by
    intro pre
    have hpref0 := taoSection7QPrefixFactor_nonneg epsilon W start pre
    have hpref1 := taoSection7QPrefixFactor_le_one hepsilon W start pre
    have hpayload :
        taoSection7QPrefixFactor epsilon W start pre * F (f pre) ≤
          F (f pre) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpref1) (hF0 (f pre))]
    exact mul_le_mul_of_nonneg_left hpayload ENNReal.toReal_nonneg
  have hleft : Summable fun pre : List TaoSection7RenewalPoint =>
      (p pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre * F (f pre)) :=
    Summable.of_nonneg_of_le
      (fun pre => mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg
          (taoSection7QPrefixFactor_nonneg epsilon W start pre)
          (hF0 (f pre))))
      hpoint hright
  calc
    (∑' pre : List TaoSection7RenewalPoint,
      (lemma77CanonicalFirstPassagePrefixPMF start gap pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre *
          F (lemma77EndpointOfPrefix start pre))) =
        ∑' pre : List TaoSection7RenewalPoint,
          (p pre).toReal *
            (taoSection7QPrefixFactor epsilon W start pre * F (f pre)) := by
          rfl
    _ ≤ ∑' pre : List TaoSection7RenewalPoint,
        (p pre).toReal * F (f pre) := hleft.tsum_le_tsum hpoint hright
    _ = ∑' x : ℕ × ℤ,
        (lemma77CanonicalFirstPassageEndpointPMF start gap x).toReal * F x := by
          simpa [p, f, lemma77CanonicalFirstPassageEndpointPMF] using
            htransport.2.2.symm

/-- The source actual stopped `Q` is bounded by the canonical expectation of
actual `Q` at the absolute endpoint. -/
theorem taoSection7SourceActualQ_le_canonicalFirstPassageEndpointExpectation
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    taoSection7SourceActualQ n xi epsilon start ≤
      ∑' x : ℕ × ℤ,
        (lemma77CanonicalFirstPassageEndpointPMF start gap x).toReal *
          taoSection7SourceActualQ n xi epsilon
            (lemma77RenewalPointOfRelativeEndpoint start x) := by
  have hQ := taoSection7SourceActualQ_bounded01
    (n := n) (xi := xi) hepsilon
  rw [taoSection7SourceActualQ_eq_canonicalFirstPassageExpectation
    hepsilon start gap]
  unfold taoSection7CanonicalFirstPassageStoppedExpectation
  simpa [lemma77RenewalPointOfRelativeEndpoint_endpointOfPrefix] using
    (taoSection7CanonicalFirstPassagePrefixFactor_endpointPayload_le
      hepsilon (taoSection7SourceActualW n xi epsilon) start gap
      (fun x => taoSection7SourceActualQ n xi epsilon
        (lemma77RenewalPointOfRelativeEndpoint start x))
      (fun x => (hQ (lemma77RenewalPointOfRelativeEndpoint start x)).1)
      (fun x => (hQ (lemma77RenewalPointOfRelativeEndpoint start x)).2))

end

end Tao
end Erdos1135
