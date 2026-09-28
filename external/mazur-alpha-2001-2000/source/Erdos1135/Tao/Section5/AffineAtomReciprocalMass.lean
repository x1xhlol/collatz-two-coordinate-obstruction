import Erdos1135.Tao.Section5.AffineAtomPointMass
import Erdos1135.Tao.Syracuse.AffineReciprocal

/-!
# Section 5 Exact Reciprocal Atom Masses

This leaf rewrites the compatible real affine-atom mass using the exact affine
reciprocal.  The source normalizer and the denominator `M - F` remain exact.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- A positive odd source has its usual harmonic weight. -/
theorem logNatWeight_taoOddNat_eq_one_div (N : TaoOddNat) :
    logNatWeight N.1 = (1 : ℝ) / (N.1 : ℝ) := by
  have hNpos : 0 < N.1 := Odd.pos N.2
  rw [logNatWeight]
  simp only [if_neg hNpos.ne']
  rw [logWeight]
  norm_num [Nat.sub_add_cancel hNpos]

/-- Exact real atom mass after rewriting the one source reciprocal.  The
geometric list mass occurs once, as part of `1 / N`, not as an additional
probability factor. -/
theorem taoSection5ClosedAffineAtom_outerMass_eq_reciprocal
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
        (((3 : ℝ) ^ (i.1.1 - taoSection5M0 B) *
              geom2PNatListMass i.2.1.1) /
            ((i.2.2.1 : ℝ) - (taoOffsetList i.2.1.1 : ℝ))) /
          logFinsetMass
            (oddLogWindow
              (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch))
      else 0 := by
  classical
  rw [taoSection5ClosedAffineAtom_outerMass_eq_candidate facts hmass i]
  by_cases hcompat :
      (i.2.2.1 : ZMod (3 ^ (i.1.1 - taoSection5M0 B))) =
        taoAffineOffsetZMod
          (i.1.1 - taoSection5M0 B) i.2.1.1
  · simp only [if_pos hcompat]
    obtain ⟨N, _hwindow, hAtom⟩ :=
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
    rw [hCandidate, logNatWeight_taoOddNat_eq_one_div]
    rw [taoAffList_reciprocal htyp.1 hAff]
  · simp only [if_neg hcompat]

end

end Tao
end Erdos1135
