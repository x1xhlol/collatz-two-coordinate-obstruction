import Erdos1135.Tao.Section3
import Erdos1135.Tao.Probability.LogWindowResidue

/-!
# Section 5 No-Hit Event Map

This leaf transports a finite logarithmic-window no-hit event into an
arbitrary event of the actual Proposition 1.9 valuation law.  It records only
the two deterministic PMF map/preimage steps; deterministic descent and the
event-probability comparison remain separate consumers.
-/

namespace Erdos1135
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
end Erdos1135
