/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QFiniteIteration
import Erdos1135SecondScale.Tao.Renewal.SourceActualQ

/-!
# Source Actual Q Finite-Horizon Iteration

This thin leaf specializes deterministic-horizon actual-`Q` iteration to
Tao's source cutoff predicate and samples the prefix from any longer iid Hold
master.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Source actual `Q` after `P` fresh steps, represented on a length-`J` iid
Hold master with `P ≤ J`. -/
theorem taoSection7SourceActualQ_eq_holdListContinuation_master_of_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {P J : ℕ} (hPJ : P ≤ J)
    (start : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon start =
      ∑' full : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF J full).toReal *
          (taoSection7QPrefixFactor epsilon
              (taoSection7SourceActualW n xi epsilon)
              start (full.take P) *
            taoSection7SourceActualQ n xi epsilon
              (taoSection7RenewalPathPoint start full P)) := by
  exact taoSection7ActualQ_eq_holdListQContinuationExpectation_master_of_le
    hPJ hepsilon (taoSection7SourceActualQ_finiteLimit hepsilon) start

/-- Source actual `Q` iteration on the canonical Lemma 7.9 horizon
`J = n / 2`. -/
theorem taoSection7SourceActualQ_eq_halfHoldListContinuation_of_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {P : ℕ} (hP : P ≤ n / 2)
    (start : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon start =
      ∑' full : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF (n / 2) full).toReal *
          (taoSection7QPrefixFactor epsilon
              (taoSection7SourceActualW n xi epsilon)
              start (full.take P) *
            taoSection7SourceActualQ n xi epsilon
              (taoSection7RenewalPathPoint start full P)) :=
  taoSection7SourceActualQ_eq_holdListContinuation_master_of_le
    hepsilon hP start

end

end Tao
end Erdos1135SecondScale
