import Erdos1135.Tao.Renewal.Outer754SourceWeight
import Erdos1135.Tao.Renewal.PMFExpectationThreeRegion
import Erdos1135.Tao.Renewal.QEndpointFreshCount
import Erdos1135.Tao.Renewal.QEndpointFreshTower

/-!
# Endpoint/Fresh Zero-Safe Closeout

This leaf places Tao's outer `(7.54)` source weight on the canonical
endpoint/fresh carrier. It proves the supported payload bound and combines it
with the countable expectation tower without cancelling the possibly-zero
previous `Q_m` factor.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Prefix-times-continuation payload in the endpoint/fresh source-Q tower. -/
noncomputable def lemma79EndpointFreshContinuationPayload
    (n P : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (entry : TaoSection7RenewalPoint) :
    ((ℕ × ℤ) × List TaoSection7RenewalPoint) → ℝ :=
  fun atom =>
    taoSection7QPrefixFactor epsilon
        (taoSection7SourceActualW n xi epsilon)
        (lemma79EndpointFreshOrigin entry atom) (atom.2.take P) *
      taoSection7SourceActualQ n xi epsilon
        (taoSection7RenewalPathPoint
          (lemma79EndpointFreshOrigin entry atom) atom.2 P)

/-- Canonical endpoint/fresh specialization of the source weight in Tao's
outer `(7.54)` expectation. -/
noncomputable def lemma79EndpointFreshOuter754Weight
    (n A m P : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (entry : TaoSection7RenewalPoint) :
    ((ℕ × ℤ) × List TaoSection7RenewalPoint) → ℝ :=
  taoSection7Case3Outer754SourceWeight A m P epsilon
    (lemma79EndpointFreshHorizontalAdvance P)
    (fun atom =>
      taoSection7Case3SourceCutoffPointW
        (lemma79EndpointFreshPointAt entry atom)
        n xi epsilon (n / 2))

/-- On every supported atom, the source-Q tower payload is bounded by the
constant-first normalized outer weight. -/
theorem lemma79CanonicalEndpointFreshPMF_payload_le_outer754Weight
    {n A m P J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m)
    {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hPJ : P ≤ J)
    (hne : lemma79CanonicalEndpointFreshPMF J entry gap atom ≠ 0) :
    lemma79EndpointFreshContinuationPayload n P xi epsilon entry atom ≤
      (((m : ℝ) ^ A)⁻¹ *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) *
        lemma79EndpointFreshOuter754Weight
          n A m P xi epsilon entry atom := by
  let W :
      ((ℕ × ℤ) × List TaoSection7RenewalPoint) → ℕ → Prop :=
    fun z =>
      taoSection7Case3SourceCutoffPointW
        (lemma79EndpointFreshPointAt entry z)
        n xi epsilon (n / 2)
  have hfactor :
      taoSection7QPrefixFactor epsilon
          (taoSection7SourceActualW n xi epsilon)
          (lemma79EndpointFreshOrigin entry atom) (atom.2.take P) =
        taoSection7Case3Outer754SourceExponentialFactor
          P epsilon W atom := by
    simpa [W, taoSection7Case3Outer754SourceExponentialFactor,
      taoSection7Case3Outer754ExponentialFactor] using
      (lemma79CanonicalEndpointFreshPMF_sourcePrefixFactor_eq_exp_windowWhiteCount
        (n := n) (J := J) (P := P) (xi := xi)
        (epsilon := epsilon) (entry := entry) (gap := gap)
        (atom := atom) hPJ hne)
  have hQ :=
    lemma79CanonicalEndpointFreshPMF_actualQ_at_le_normalized
      (n := n) (A := A) (m := m) (P := P) (J := J)
      (xi := xi) (epsilon := epsilon) (entry := entry)
      (gap := gap) (atom := atom)
      hepsilon hm hboundary hne
  unfold lemma79EndpointFreshContinuationPayload
  rw [hfactor]
  calc
    taoSection7Case3Outer754SourceExponentialFactor P epsilon W atom *
          taoSection7SourceActualQ n xi epsilon
            (taoSection7RenewalPathPoint
              (lemma79EndpointFreshOrigin entry atom) atom.2 P) ≤
        taoSection7Case3Outer754SourceExponentialFactor P epsilon W atom *
          (((m : ℝ) ^ A)⁻¹ *
              taoSection7SourceActualQmAtCutoff
                n A (m - 1) xi epsilon *
            taoSection7Case3Outer754HorizontalFactor A m
              (lemma79EndpointFreshHorizontalAdvance P) atom) :=
      mul_le_mul_of_nonneg_left hQ (Real.exp_nonneg _)
    _ = (((m : ℝ) ^ A)⁻¹ *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) *
        lemma79EndpointFreshOuter754Weight
          n A m P xi epsilon entry atom := by
      simp only [lemma79EndpointFreshOuter754Weight,
        taoSection7Case3Outer754SourceWeight]
      ac_rfl

/-- Direct countable endpoint/fresh closeout for the source boundary value.
The weight expectation hypotheses are designed to be supplied by the checked
three-region theorem; the conclusion remains valid when the previous `Q_m`
factor vanishes. -/
theorem taoSection7SourceActualQ_le_endpointFreshOuter754_of_expectation_le_one
    {n A m P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hm : 1 ≤ m) (hP : P ≤ n / 2)
    (entry : TaoSection7RenewalPoint) (gap : ℕ)
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hsumWeight :
      Summable fun atom =>
        (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap atom).toReal *
          lemma79EndpointFreshOuter754Weight
            n A m P xi epsilon entry atom)
    (hweight_le_one :
      taoSection7PMFExpectation
          (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap)
          (lemma79EndpointFreshOuter754Weight
            n A m P xi epsilon entry) ≤ 1) :
    taoSection7SourceActualQ n xi epsilon entry ≤
      ((m : ℝ) ^ A)⁻¹ *
        taoSection7SourceActualQmAtCutoff
          n A (m - 1) xi epsilon := by
  let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
  let payload := lemma79EndpointFreshContinuationPayload
    n P xi epsilon entry
  let weight := lemma79EndpointFreshOuter754Weight
    n A m P xi epsilon entry
  let c : ℝ := ((m : ℝ) ^ A)⁻¹ *
    taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by positivity)
      (taoSection7SourceActualQmAtCutoff_nonneg hepsilon)
  have hpayload0 : ∀ atom, μ atom ≠ 0 → 0 ≤ payload atom := by
    intro atom _hne
    dsimp [payload, lemma79EndpointFreshContinuationPayload]
    exact mul_nonneg
      (taoSection7QPrefixFactor_nonneg epsilon
        (taoSection7SourceActualW n xi epsilon)
        (lemma79EndpointFreshOrigin entry atom) (atom.2.take P))
      (taoSection7SourceActualQ_nonneg hepsilon
        (taoSection7RenewalPathPoint
          (lemma79EndpointFreshOrigin entry atom) atom.2 P))
  have hdom : ∀ atom, μ atom ≠ 0 → payload atom ≤ c * weight atom := by
    intro atom hne
    exact lemma79CanonicalEndpointFreshPMF_payload_le_outer754Weight
      (n := n) (A := A) (m := m) (P := P) (J := n / 2)
      (xi := xi) (epsilon := epsilon) (entry := entry) (gap := gap)
      (atom := atom) hepsilon hm hboundary hP hne
  have hclose := taoSection7PMFExpectation_zeroSafe_closeout
    μ hc hpayload0
      (by simpa [μ, weight] using hsumWeight)
      hdom
      (by simpa [μ, weight] using hweight_le_one)
  calc
    taoSection7SourceActualQ n xi epsilon entry ≤
        taoSection7PMFExpectation μ payload := by
      simpa [μ, payload, lemma79EndpointFreshContinuationPayload,
        lemma79EndpointFreshOrigin] using
        (taoSection7SourceActualQ_le_endpointFreshContinuation
          (n := n) (xi := xi) (epsilon := epsilon)
          hepsilon hP entry gap)
    _ ≤ c := hclose.2
    _ = ((m : ℝ) ^ A)⁻¹ *
        taoSection7SourceActualQmAtCutoff
          n A (m - 1) xi epsilon := rfl

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
