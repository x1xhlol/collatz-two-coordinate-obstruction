/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshDomain
import Erdos1135SecondScale.Tao.Renewal.QPrefixFactor
import Erdos1135SecondScale.Tao.Renewal.Prop78Case3CutoffAlignment

/-!
# Endpoint/Fresh Prefix Count

This leaf identifies the endpoint-exclusive `Q` prefix factor with the
exponential of the corresponding low-window white count.  The generic theorem
keeps the necessary list-length boundary explicit; the carrier theorem obtains
that boundary from nonzero endpoint/fresh mass.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The endpoint-exclusive prefix factor pays exactly the white visits at
offsets `0, ..., P - 1`.  The length premise prevents the total renewal path
from becoming stationary before the requested window ends. -/
theorem taoSection7QPrefixFactor_take_eq_exp_windowWhiteCount
    (epsilon : ℝ)
    (W : TaoSection7RenewalPoint → Prop) [DecidablePred W]
    (start : TaoSection7RenewalPoint)
    (fresh : List TaoSection7RenewalPoint) (P : ℕ)
    (hP : P ≤ fresh.length) :
    taoSection7QPrefixFactor epsilon W start (fresh.take P) =
      Real.exp (-(epsilon ^ 3) *
        (taoSection7Case3WindowWhiteCount
          (fun p => W (taoSection7RenewalPathPoint start fresh p)) P : ℝ)) := by
  induction P generalizing start fresh with
  | zero =>
      simp [taoSection7Case3WindowWhiteCount]
  | succ P ih =>
      cases fresh with
      | nil =>
          simp at hP
      | cons h fresh =>
          have hP' : P ≤ fresh.length := by
            simpa using hP
          have hcount :
              taoSection7Case3WindowWhiteCount
                  (fun p =>
                    W (taoSection7RenewalPathPoint start (h :: fresh) p))
                  (P + 1) =
                taoSection7QWhiteIndicator W start +
                  taoSection7Case3WindowWhiteCount
                    (fun p =>
                      W (taoSection7RenewalPathPoint (start + h) fresh p))
                    P := by
            unfold taoSection7Case3WindowWhiteCount
            rw [Finset.sum_range_succ']
            simp only [taoSection7RenewalPathPoint_zero,
              taoSection7RenewalPathPoint_cons_succ,
              taoSection7QWhiteIndicator]
            by_cases hW : W start <;> simp [hW, Nat.add_comm]
          rw [List.take_succ_cons, taoSection7QPrefixFactor_cons,
            ih (start := start + h) (fresh := fresh) hP',
            taoSection7QWhiteFactor_eq_exp_indicator,
            ← Real.exp_add, hcount, Nat.cast_add]
          congr 1
          ring

open TaoSection7Lemma77

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- On a supported endpoint/fresh atom, the source `Q` prefix factor is the
exponential of the source cutoff-white count on the full requested window. -/
theorem lemma79CanonicalEndpointFreshPMF_sourcePrefixFactor_eq_exp_windowWhiteCount
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hPJ : P ≤ J)
    (hne : lemma79CanonicalEndpointFreshPMF J entry gap atom ≠ 0) :
    taoSection7QPrefixFactor epsilon
        (taoSection7SourceActualW n xi epsilon)
        (lemma79EndpointFreshOrigin entry atom) (atom.2.take P) =
      Real.exp (-(epsilon ^ 3) *
        (taoSection7Case3WindowWhiteCount
          (taoSection7Case3SourceCutoffPointW
            (lemma79EndpointFreshPointAt entry atom)
            n xi epsilon (n / 2)) P : ℝ)) := by
  classical
  have hlength :=
    (lemma79CanonicalEndpointFreshPMF_nonzero_support hne).2.2
  have hP : P ≤ atom.2.length := by omega
  have hcount :
      taoSection7Case3WindowWhiteCount
          (fun p =>
            taoSection7SourceActualW n xi epsilon
              (taoSection7RenewalPathPoint
                (lemma79EndpointFreshOrigin entry atom) atom.2 p)) P =
        taoSection7Case3WindowWhiteCount
          (taoSection7Case3SourceCutoffPointW
            (lemma79EndpointFreshPointAt entry atom)
            n xi epsilon (n / 2)) P := by
    apply taoSection7Case3WindowWhiteCount_congr_range
    intro p _hp
    simpa [lemma79EndpointFreshPointAt] using
      (taoSection7Case3_sourceActualW_iff_sourceCutoffPointW_toPoint
        (renewalAt := fun q =>
          taoSection7RenewalPathPoint
            (lemma79EndpointFreshOrigin entry atom) atom.2 q)
        (n := n) (p := p) (xi := xi) (epsilon := epsilon))
  rw [taoSection7QPrefixFactor_take_eq_exp_windowWhiteCount
    epsilon (taoSection7SourceActualW n xi epsilon)
    (lemma79EndpointFreshOrigin entry atom) atom.2 P hP, hcount]

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
