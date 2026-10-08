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
import Erdos1135Predecessor.Tao.Renewal.QStoppedEndpoint
import Erdos1135Predecessor.Tao.Renewal.SourceActualQIteration

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

theorem taoSection7PMFExpectation_bind_pair_eq
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (F : Pre → Tail → ℝ)
    (hF0 : ∀ pre tail, 0 ≤ F pre tail)
    (hF1 : ∀ pre tail, F pre tail ≤ 1) :
    taoSection7PMFExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => F pair.1 pair.2) =
      ∑' pre, (pi pre).toReal *
        ∑' tail, (tau tail).toReal * F pre tail := by
  let mu := pi.bind fun pre => tau.map fun tail => (pre, tail)
  let payload : Pre × Tail → ℝ := fun pair => F pair.1 pair.2
  have hsum : Summable fun pair : Pre × Tail =>
      (mu pair).toReal * payload pair :=
    taoSection7PMFExpectation_summable_of_bounded01 mu payload
      (fun pair => hF0 pair.1 pair.2)
      (fun pair => hF1 pair.1 pair.2)
  have hfiber : ∀ pre, Summable fun tail =>
      (mu (pre, tail)).toReal * payload (pre, tail) := by
    intro pre
    have hinj : Function.Injective (fun tail : Tail => (pre, tail)) := by
      intro x y hxy
      exact congrArg Prod.snd hxy
    simpa [Function.comp_apply] using hsum.comp_injective hinj
  unfold taoSection7PMFExpectation
  change (∑' pair : Pre × Tail, (mu pair).toReal * payload pair) = _
  rw [hsum.tsum_prod' hfiber]
  apply tsum_congr
  intro pre
  calc
    (∑' tail, (mu (pre, tail)).toReal * payload (pre, tail)) =
        ∑' tail, ((pi pre).toReal * (tau tail).toReal) * F pre tail := by
      apply tsum_congr
      intro tail
      simp only [mu, payload]
      rw [lemma79_prefixFreshTail_bind_apply, ENNReal.toReal_mul]
    _ = ∑' tail, (pi pre).toReal *
        ((tau tail).toReal * F pre tail) := by
      apply tsum_congr
      intro tail
      ring
    _ = (pi pre).toReal *
        ∑' tail, (tau tail).toReal * F pre tail := by
      rw [tsum_mul_left]

theorem taoSection7SourceActualQ_le_endpointFreshContinuation_master_of_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {P J : ℕ} (hPJ : P ≤ J)
    (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    taoSection7SourceActualQ n xi epsilon entry ≤
      taoSection7PMFExpectation
        (lemma79CanonicalEndpointFreshPMF J entry gap)
        (fun pair =>
          let origin :=
            lemma77RenewalPointOfRelativeEndpoint entry pair.1
          taoSection7QPrefixFactor epsilon
              (taoSection7SourceActualW n xi epsilon)
              origin (pair.2.take P) *
            taoSection7SourceActualQ n xi epsilon
              (taoSection7RenewalPathPoint origin pair.2 P)) := by
  let endpointPMF := lemma77CanonicalFirstPassageEndpointPMF entry gap
  let freshPMF := taoSection7HoldListPMF J
  let origin : (ℕ × ℤ) → TaoSection7RenewalPoint :=
    lemma77RenewalPointOfRelativeEndpoint entry
  let payload : (ℕ × ℤ) → List TaoSection7RenewalPoint → ℝ :=
    fun endpoint fresh =>
      taoSection7QPrefixFactor epsilon
          (taoSection7SourceActualW n xi epsilon)
          (origin endpoint) (fresh.take P) *
        taoSection7SourceActualQ n xi epsilon
          (taoSection7RenewalPathPoint (origin endpoint) fresh P)
  have hQ := taoSection7SourceActualQ_bounded01
    (n := n) (xi := xi) hepsilon
  have hpayload0 : ∀ endpoint fresh, 0 ≤ payload endpoint fresh := by
    intro endpoint fresh
    exact mul_nonneg
      (taoSection7QPrefixFactor_nonneg epsilon
        (taoSection7SourceActualW n xi epsilon)
        (origin endpoint) (fresh.take P))
      (hQ (taoSection7RenewalPathPoint (origin endpoint) fresh P)).1
  have hpayload1 : ∀ endpoint fresh, payload endpoint fresh ≤ 1 := by
    intro endpoint fresh
    have hpref := taoSection7QPrefixFactor_le_one hepsilon
      (taoSection7SourceActualW n xi epsilon)
      (origin endpoint) (fresh.take P)
    have htail :=
      (hQ (taoSection7RenewalPathPoint (origin endpoint) fresh P)).2
    calc
      payload endpoint fresh ≤ 1 * 1 := by
        exact mul_le_mul hpref htail
          (hQ (taoSection7RenewalPathPoint (origin endpoint) fresh P)).1
          (by norm_num)
      _ = 1 := by norm_num
  have hbind := taoSection7PMFExpectation_bind_pair_eq
    endpointPMF freshPMF payload hpayload0 hpayload1
  calc
    taoSection7SourceActualQ n xi epsilon entry ≤
        ∑' endpoint, (endpointPMF endpoint).toReal *
          taoSection7SourceActualQ n xi epsilon (origin endpoint) := by
      simpa [endpointPMF, origin] using
        (taoSection7SourceActualQ_le_canonicalFirstPassageEndpointExpectation
          hepsilon entry gap)
    _ = ∑' endpoint, (endpointPMF endpoint).toReal *
        ∑' fresh, (freshPMF fresh).toReal * payload endpoint fresh := by
      apply tsum_congr
      intro endpoint
      rw [taoSection7SourceActualQ_eq_holdListContinuation_master_of_le
        hepsilon hPJ (origin endpoint)]
    _ = taoSection7PMFExpectation
        (lemma79CanonicalEndpointFreshPMF J entry gap)
        (fun pair =>
          let restarted :=
            lemma77RenewalPointOfRelativeEndpoint entry pair.1
          taoSection7QPrefixFactor epsilon
              (taoSection7SourceActualW n xi epsilon)
              restarted (pair.2.take P) *
            taoSection7SourceActualQ n xi epsilon
              (taoSection7RenewalPathPoint restarted pair.2 P)) := by
      simpa [lemma79CanonicalEndpointFreshPMF, endpointPMF, freshPMF,
        origin, payload] using hbind.symm

theorem taoSection7SourceActualQ_le_endpointFreshContinuation
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {P : ℕ} (hP : P ≤ n / 2)
    (entry : TaoSection7RenewalPoint) (gap : ℕ) :
    taoSection7SourceActualQ n xi epsilon entry ≤
      taoSection7PMFExpectation
        (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap)
        (fun pair =>
          let origin :=
            lemma77RenewalPointOfRelativeEndpoint entry pair.1
          taoSection7QPrefixFactor epsilon
              (taoSection7SourceActualW n xi epsilon)
              origin (pair.2.take P) *
            taoSection7SourceActualQ n xi epsilon
              (taoSection7RenewalPathPoint origin pair.2 P)) :=
  taoSection7SourceActualQ_le_endpointFreshContinuation_master_of_le
    hepsilon hP entry gap

end

end Tao

end Erdos1135Predecessor
