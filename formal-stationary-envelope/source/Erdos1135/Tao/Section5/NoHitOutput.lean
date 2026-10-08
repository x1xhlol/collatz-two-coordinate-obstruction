import Erdos1135.Tao.Section5.DeterministicDescent
import Erdos1135.Tao.Section5.NoHitMap
import Erdos1135.Tao.Section5.Prop19Output
import Erdos1135.Tao.Probability.FullL1

/-!
# Section 5 Native No-Hit Output

This leaf assembles the deterministic strict-low implication, the actual-law
event map, the full-L1 comparison, and the ideal Geom(2) tail at one fixed
threshold.  It contains no polynomial-rate conversion or legacy facade
adapter.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open Filter

/-- Raw error supplied by the strict ideal tail and the fixed Proposition 1.9
valuation approximation. -/
noncomputable def taoSection5NoHitError (B : ℕ) : ℝ :=
  Real.exp (-((taoSection5N0 B : ℝ) / 3200)) +
    4 * (2 : ℝ) ^
      (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ)))

/-- Fixed-threshold native no-hit estimate.  The positive-mass proof supplied
by a consumer is identified once with the proof stored in the Proposition 1.9
packet, before either source PMF is constructed. -/
theorem taoSection5_noHitWindowProb_le_error_of_inputs
    {B : ℕ} (descent : TaoSection5DescentScaleFacts B)
    (prop19 : TaoSection5LogWindowProp19Output B)
    (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch))) :
    syracuseNoHitWindowProb B
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass ≤
      taoSection5NoHitError B := by
  have hmassEq : hmass = prop19.schedule.mass_pos branch :=
    Subsingleton.elim _ _
  subst hmass
  let lo := taoSection5SourceLo B branch
  let hi := taoSection5SourceHi B branch
  let n := taoSection5N0 B
  let source := oddLogWindowOddNatPMF lo hi (prop19.schedule.mass_pos branch)
  let E := taoLowValuationWeightEvent n
  have hmap :
      syracuseNoHitWindowProb B lo hi (prop19.schedule.mass_pos branch) ≤
        ((taoProp19ActualValuationLaw source n).toOuterMeasure E).toReal := by
    apply syracuseNoHitWindowProb_le_actualValuationLaw_event
    intro N hno
    apply descent.actualValuations_mem_low_of_not_hitsAtMost
      (N := oddLogWindowValueToOddNat N)
    · exact N.property
    · simpa only [syracuseNoHitAtMost, Set.mem_setOf_eq] using hno
  have hvaluation := prop19.valuationBound branch
  unfold taoProp19ValuationTV at hvaluation
  have hcompare :
      ((taoProp19ActualValuationLaw source n).toOuterMeasure E).toReal ≤
        ((geom2PNatListPMF n).toOuterMeasure E).toReal +
          4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) := by
    apply pmfOuterMass_le_add_of_taoPMFFullL1_le
    simpa only [source, n, lo, hi] using hvaluation
  have hideal := geom2PNatListPMF_lowWeightEvent_le_exp n
  calc
    syracuseNoHitWindowProb B lo hi (prop19.schedule.mass_pos branch) ≤
        ((taoProp19ActualValuationLaw source n).toOuterMeasure E).toReal := hmap
    _ ≤ ((geom2PNatListPMF n).toOuterMeasure E).toReal +
        4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) := hcompare
    _ ≤ Real.exp (-((n : ℝ) / 3200)) +
        4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) := by
      exact add_le_add (by simpa only [E] using hideal) le_rfl
    _ = taoSection5NoHitError B := by
      rfl

/-- Native provenance and branchwise no-hit output at one common threshold. -/
structure TaoSection5NoHitOutput (B : ℕ) : Prop where
  prop19 : TaoSection5LogWindowProp19Output B
  descent : TaoSection5DescentScaleFacts B
  noHit_le : ∀ branch : TaoSection5SourceBranch,
    ∀ hmass : 0 < logFinsetMass
      (oddLogWindow (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch)),
      syracuseNoHitWindowProb B
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) hmass ≤
        taoSection5NoHitError B

theorem TaoSection5NoHitOutput.of_inputs
    {B : ℕ} (prop19 : TaoSection5LogWindowProp19Output B)
    (descent : TaoSection5DescentScaleFacts B) :
    TaoSection5NoHitOutput B :=
  { prop19 := prop19
    descent := descent
    noHit_le := fun branch hmass =>
      taoSection5_noHitWindowProb_le_error_of_inputs
        descent prop19 branch hmass }

/-- Both canonical source branches carry the native no-hit estimate for all
sufficiently large common thresholds. -/
theorem eventually_taoSection5NoHitOutput :
    ∀ᶠ B : ℕ in atTop, TaoSection5NoHitOutput B := by
  filter_upwards [eventually_taoSection5LogWindowProp19Output,
    eventually_taoSection5DescentScaleFacts] with B prop19 descent
  exact TaoSection5NoHitOutput.of_inputs prop19 descent

end

end Tao
end Erdos1135
