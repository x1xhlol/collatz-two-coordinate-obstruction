/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section3
import Erdos1135SecondScale.Tao.Probability.LogWindowResidue

/-!
# Section 5 No-Hit Event Map

This leaf transports a finite logarithmic-window no-hit event into an
arbitrary event of the actual Proposition 1.9 valuation law.  It records only
the two deterministic PMF map/preimage steps; deterministic descent and the
event-probability comparison remain separate consumers.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- A pointwise no-hit-to-valuation-event implication transports the finite
source probability into the actual valuation-law event mass. -/
theorem syracuseNoHitWindowProb_le_actualValuationLaw_event
    (B lo hi n : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (E : Set (List ℕ+))
    (hpoint : ∀ N : {N : ℕ // N ∈ oddLogWindow lo hi},
      (N : ℕ) ∈ syracuseNoHitAtMost B →
        syracuseValuationPNatList n
          (oddLogWindowValueToOddNat N).1
          (oddLogWindowValueToOddNat N).2 ∈ E) :
    syracuseNoHitWindowProb B lo hi hmass ≤
      ((taoProp19ActualValuationLaw
        (oddLogWindowOddNatPMF lo hi hmass) n).toOuterMeasure E).toReal := by
  unfold syracuseNoHitWindowProb
  calc
    pmfProb (oddLogWindowPMF lo hi hmass)
        {N : {N : ℕ // N ∈ oddLogWindow lo hi} |
          (N : ℕ) ∈ syracuseNoHitAtMost B} ≤
      pmfProb (oddLogWindowPMF lo hi hmass)
        {N : {N : ℕ // N ∈ oddLogWindow lo hi} |
          syracuseValuationPNatList n
            (oddLogWindowValueToOddNat N).1
            (oddLogWindowValueToOddNat N).2 ∈ E} := by
      exact pmfProb_mono (oddLogWindowPMF lo hi hmass) hpoint
    _ = ((taoProp19ActualValuationLaw
          (oddLogWindowOddNatPMF lo hi hmass) n).toOuterMeasure E).toReal := by
      rw [pmfProb_eq_toOuterMeasure_toReal]
      unfold taoProp19ActualValuationLaw oddLogWindowOddNatPMF
      rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
      apply congrArg ENNReal.toReal
      apply congrArg (oddLogWindowPMF lo hi hmass).toOuterMeasure
      ext N
      rfl

end Tao
end Erdos1135SecondScale
