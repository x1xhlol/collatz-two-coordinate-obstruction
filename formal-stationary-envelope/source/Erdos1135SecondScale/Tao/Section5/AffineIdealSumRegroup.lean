/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.AffineAtomDenominatorComparison
import Erdos1135SecondScale.Tao.Section5.PayloadFreeCoefficient

/-!
# Section 5 Exact Ideal Atom-Sum Regrouping

This leaf reindexes the denominator-simplified dependent atom sum into
scheduled times, closed-typical tuples, and the elementary payload-free
coefficient.  It keeps the source normalizer exact and does not remove the
typicality gate.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- For fixed scheduled time and tuple, summing ideal endpoint terms is the
geometric tuple mass times the payload-free residue coefficient. -/
theorem taoSection5_sum_idealAffineEndpointMass_eq_coefficient
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (n : {n // n ∈ taoSection5PassTimes B branch})
    (as : {as // as ∈
      taoSection5TypicalTuples B (n.1 - taoSection5M0 B)}) :
    (∑ M : {M // M ∈ taoSection5EPrime B E},
        taoSection5IdealAffineAtomMass hmass ⟨n, (as, M)⟩) =
      (1 / logFinsetMass
          (oddLogWindow
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch))) *
        (geom2PNatListMass as.1 *
          taoSection5PayloadFreeCoefficient
            (n.1 - taoSection5M0 B) (taoSection5EPrime B E)
            (taoAffineOffsetZMod
              (n.1 - taoSection5M0 B) as.1)) := by
  classical
  unfold taoSection5IdealAffineAtomMass
  unfold taoSection5PayloadFreeCoefficient
  let endpointTerm : ℕ → ℝ := fun M =>
    if (M : ZMod (3 ^ (n.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod (n.1 - taoSection5M0 B) as.1 then
      (((3 : ℝ) ^ (n.1 - taoSection5M0 B) *
          geom2PNatListMass as.1) / (M : ℝ)) /
        logFinsetMass
          (oddLogWindow
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch))
    else 0
  change
    (∑ M : {M // M ∈ taoSection5EPrime B E}, endpointTerm M.1) = _
  rw [Finset.sum_coe_sort (taoSection5EPrime B E) endpointTerm]
  dsimp only [endpointTerm]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _hM
  by_cases hcompat :
      (M : ZMod (3 ^ (n.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod (n.1 - taoSection5M0 B) as.1
  · simp only [if_pos hcompat]
    ring
  · simp only [if_neg hcompat]

/-- Exact finite regrouping of the complete ideal dependent atom sum.  The
coefficient already contains `3^q`; the tuple mass and source normalizer each
occur once outside it. -/
theorem taoSection5_sum_idealAffineAtomMass_eq_regrouped
    {B : ℕ} (branch : TaoSection5SourceBranch) (E : Set ℕ)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch))) :
    (∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
        taoSection5IdealAffineAtomMass hmass i) =
      (1 / logFinsetMass
          (oddLogWindow
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch))) *
        ∑ n : {n // n ∈ taoSection5PassTimes B branch},
          ∑ as : {as // as ∈
              taoSection5TypicalTuples B (n.1 - taoSection5M0 B)},
            geom2PNatListMass as.1 *
              taoSection5PayloadFreeCoefficient
                (n.1 - taoSection5M0 B) (taoSection5EPrime B E)
                (taoAffineOffsetZMod
                  (n.1 - taoSection5M0 B) as.1) := by
  classical
  calc
    (∑ i : TaoSection5ClosedAffineAtomIndex B branch E,
        taoSection5IdealAffineAtomMass hmass i) =
        ∑ n : {n // n ∈ taoSection5PassTimes B branch},
          ∑ p :
              {as // as ∈ taoSection5TypicalTuples B
                (n.1 - taoSection5M0 B)} ×
                {M // M ∈ taoSection5EPrime B E},
            taoSection5IdealAffineAtomMass hmass ⟨n, p⟩ := by
      exact Fintype.sum_sigma _
    _ = ∑ n : {n // n ∈ taoSection5PassTimes B branch},
          ∑ as : {as // as ∈
              taoSection5TypicalTuples B (n.1 - taoSection5M0 B)},
            ∑ M : {M // M ∈ taoSection5EPrime B E},
              taoSection5IdealAffineAtomMass hmass ⟨n, (as, M)⟩ := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact Fintype.sum_prod_type _
    _ = ∑ n : {n // n ∈ taoSection5PassTimes B branch},
          ∑ as : {as // as ∈
              taoSection5TypicalTuples B (n.1 - taoSection5M0 B)},
            (1 / logFinsetMass
                (oddLogWindow
                  (taoSection5SourceLo B branch)
                  (taoSection5SourceHi B branch))) *
              (geom2PNatListMass as.1 *
                taoSection5PayloadFreeCoefficient
                  (n.1 - taoSection5M0 B) (taoSection5EPrime B E)
                  (taoAffineOffsetZMod
                    (n.1 - taoSection5M0 B) as.1)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro as _has
      exact taoSection5_sum_idealAffineEndpointMass_eq_coefficient
        hmass n as
    _ = (1 / logFinsetMass
            (oddLogWindow
              (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch))) *
          ∑ n : {n // n ∈ taoSection5PassTimes B branch},
            ∑ as : {as // as ∈
                taoSection5TypicalTuples B (n.1 - taoSection5M0 B)},
              geom2PNatListMass as.1 *
                taoSection5PayloadFreeCoefficient
                  (n.1 - taoSection5M0 B) (taoSection5EPrime B E)
                  (taoAffineOffsetZMod
                    (n.1 - taoSection5M0 B) as.1) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]

end

end Tao
end Erdos1135SecondScale
