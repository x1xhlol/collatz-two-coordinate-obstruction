/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.LogWindowOddNatPoint
import Erdos1135SecondScale.Tao.Section5.AffineAtomFiber

/-!
# Section 5 Affine Atom Point Masses

This leaf evaluates one scheduled affine atom under the odd logarithmic-window
source PMF.  It keeps the exact source normalizer and stops before reciprocal
algebra, denominator approximation, or tuple-law rewrites.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Native mass of a scheduled affine atom.  A compatible atom contains the
explicit supported source candidate; an incompatible atom is empty. -/
theorem taoSection5ClosedAffineAtom_outerMeasure_eq_candidate
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (i : TaoSection5ClosedAffineAtomIndex B branch E) :
    (oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
          (taoSection5ClosedAffineAtom i) =
      if (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
          taoAffineOffsetZMod
            (i.1.1 - taoSection5M0 B) i.2.1.1 then
        ENNReal.ofReal
          (logNatWeight
              (taoAffineSourceCandidate
                (i.1.1 - taoSection5M0 B) i.2.1.1 i.2.2.1) /
            logFinsetMass
              (oddLogWindow
                (taoSection5SourceLo B branch)
                (taoSection5SourceHi B branch)))
      else 0 := by
  classical
  by_cases hcompat :
      (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod
          (i.1.1 - taoSection5M0 B) i.2.1.1
  · rw [if_pos hcompat]
    obtain ⟨N, hwindow, hAtom⟩ :=
      exists_taoSection5ClosedAffineAtom_eq_singleton_of_compatible
        facts i hcompat
    have hAff :
        taoAffList i.2.1.1 (N.1 : ℚ) = (i.2.2.1 : ℚ) := by
      change N ∈ taoSection5ClosedAffineAtom i
      rw [hAtom]
      exact Set.mem_singleton N
    have htyp := mem_taoSection5TypicalTuples_iff.mp i.2.1.2
    have hCandidate :=
      taoAffineSourceCandidate_eq_of_taoAffList_eq htyp.1 hAff
    rw [hAtom, PMF.toOuterMeasure_apply_singleton]
    rw [oddLogWindowOddNatPMF_apply_of_mem hmass N hwindow]
    simp only [hCandidate]
  · rw [if_neg hcompat]
    rw [taoSection5ClosedAffineAtom_eq_empty_of_incompatible i hcompat]
    simp

/-- Real projection of the exact scheduled affine-atom mass. -/
theorem taoSection5ClosedAffineAtom_outerMass_eq_candidate
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hmass :
      0 < logFinsetMass
        (oddLogWindow
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)))
    (i : TaoSection5ClosedAffineAtomIndex B branch E) :
    ((oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
          (taoSection5ClosedAffineAtom i)).toReal =
      if (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
          taoAffineOffsetZMod
            (i.1.1 - taoSection5M0 B) i.2.1.1 then
        logNatWeight
            (taoAffineSourceCandidate
              (i.1.1 - taoSection5M0 B) i.2.1.1 i.2.2.1) /
          logFinsetMass
            (oddLogWindow
              (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch))
      else 0 := by
  rw [taoSection5ClosedAffineAtom_outerMeasure_eq_candidate facts hmass i]
  by_cases hcompat :
      (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod
          (i.1.1 - taoSection5M0 B) i.2.1.1
  · simp only [if_pos hcompat]
    exact ENNReal.toReal_ofReal
      (div_nonneg
        (logNatWeight_nonneg
          (taoAffineSourceCandidate
            (i.1.1 - taoSection5M0 B) i.2.1.1 i.2.2.1))
        hmass.le)
  · simp only [if_neg hcompat, ENNReal.toReal_zero]

end

end Tao
end Erdos1135SecondScale
