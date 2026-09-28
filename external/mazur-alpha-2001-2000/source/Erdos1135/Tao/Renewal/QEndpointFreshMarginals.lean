import Erdos1135.Tao.Renewal.CanonicalFirstPassageHorizontal
import Erdos1135.Tao.Renewal.Lemma79EndpointFreshLaw

/-!
# Endpoint/Fresh Carrier Marginals

Exact endpoint, horizontal, and finite fresh-prefix pushforwards of the
canonical endpoint/fresh bind.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

theorem lemma79CanonicalEndpointFreshPMF_map_fst_eq
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).map Prod.fst =
      lemma77CanonicalFirstPassageEndpointPMF entry gap := by
  unfold lemma79CanonicalEndpointFreshPMF
  rw [PMF.map_bind]
  calc
    (lemma77CanonicalFirstPassageEndpointPMF entry gap).bind
        (fun endpoint =>
          ((taoSection7HoldListPMF J).map
              (fun fresh => (endpoint, fresh))).map Prod.fst) =
      (lemma77CanonicalFirstPassageEndpointPMF entry gap).bind
        (fun endpoint => PMF.pure endpoint) := by
      apply congrArg
        (PMF.bind (lemma77CanonicalFirstPassageEndpointPMF entry gap))
      funext endpoint
      rw [PMF.map_comp]
      change (taoSection7HoldListPMF J).map
        (Function.const (List TaoSection7RenewalPoint) endpoint) =
          PMF.pure endpoint
      exact PMF.map_const (taoSection7HoldListPMF J) endpoint
    _ = lemma77CanonicalFirstPassageEndpointPMF entry gap := by
      simpa using
        (PMF.bind_pure
          (lemma77CanonicalFirstPassageEndpointPMF entry gap))

theorem lemma79CanonicalEndpointFreshPMF_map_horizontal_eq
    (J : ℕ) (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).map
        (fun atom => atom.1.1) =
      lemma77CanonicalFirstPassageHorizontalPMF entry gap := by
  calc
    (lemma79CanonicalEndpointFreshPMF J entry gap).map
        (fun atom => atom.1.1) =
      ((lemma79CanonicalEndpointFreshPMF J entry gap).map Prod.fst).map
        Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = (lemma77CanonicalFirstPassageEndpointPMF entry gap).map Prod.fst := by
      rw [lemma79CanonicalEndpointFreshPMF_map_fst_eq]
    _ = lemma77CanonicalFirstPassageHorizontalPMF entry gap := rfl

theorem lemma79CanonicalEndpointFreshPMF_map_fresh_take_eq_of_le
    {P J : ℕ} (hPJ : P ≤ J)
    (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).map
        (fun atom : (ℕ × ℤ) × List TaoSection7RenewalPoint =>
          atom.2.take P) =
      taoSection7HoldListPMF P := by
  unfold lemma79CanonicalEndpointFreshPMF
  rw [PMF.map_bind]
  calc
    (lemma77CanonicalFirstPassageEndpointPMF entry gap).bind
        (fun endpoint =>
          ((taoSection7HoldListPMF J).map
              (fun fresh => (endpoint, fresh))).map
            (fun atom => atom.2.take P)) =
      (lemma77CanonicalFirstPassageEndpointPMF entry gap).bind
        (fun _ => taoSection7HoldListPMF P) := by
      apply congrArg
        (PMF.bind (lemma77CanonicalFirstPassageEndpointPMF entry gap))
      funext endpoint
      rw [PMF.map_comp]
      simpa [Function.comp_def] using
        (taoSection7HoldListPMF_map_take_eq_of_le hPJ)
    _ = taoSection7HoldListPMF P :=
      PMF.bind_const
        (lemma77CanonicalFirstPassageEndpointPMF entry gap)
        (taoSection7HoldListPMF P)

/-- Horizontal displacement depends only on the corresponding list prefix. -/
theorem lemma79HoldPrefixHorizontalDelta_take
    (P : ℕ) (fresh : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixHorizontalDelta P (fresh.take P) =
      lemma77HoldPrefixHorizontalDelta P fresh := by
  induction P generalizing fresh with
  | zero => simp [lemma77HoldPrefixHorizontalDelta]
  | succ P ih =>
      cases fresh with
      | nil => simp [lemma77HoldPrefixHorizontalDelta]
      | cons h fresh =>
          simp [lemma77HoldPrefixHorizontalDelta, ih]

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
