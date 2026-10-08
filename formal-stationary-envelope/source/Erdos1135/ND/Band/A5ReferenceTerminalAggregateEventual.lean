import Erdos1135.ND.Band.A5ReferenceTerminalAggregate
import Erdos1135.ND.Band.A5PaddedBandDiameter
import Erdos1135.Tao.Section5.AffineSourceScale
import Erdos1135.Tao.Section5.PassLostWindow

/-!
# Eventual whole-band A5 reference aggregation

This leaf chooses the single conditioned-FM1 constant before the base,
branch, band, event, time, and law parameters, then applies the checked finite
paired aggregate uniformly.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- Named whole-band reference endpoint at one base and one fixed FM1
constant.  Both laws use the same reference level and endpoint kernel. -/
def NDA5ReferenceTerminalAggregateBoundAt
    (B : ℕ) (Cband Cfm1 : ℝ) : Prop :=
  ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ),
    j < ndA5BandCount B branch →
      let m := ndA5ReferenceLevel B
      let W := ndA5TubeWidth B Cband
      let cap := 1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ))
      (|(∑ i : NDA5TerminalAtomIndex B branch Cband j E,
            ndA5HarmonicTerminalAtomNominalIdealMass i) -
          ndA5HarmonicReferencePhysicalProfile B m branch Cband j E| ≤
        2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5HarmonicReferenceNonproportionalError m Cfm1) ∧
      (|(∑ i : NDA5TerminalAtomIndex B branch Cband j E,
            ndA5FlatTerminalAtomNominalIdealMass i) -
          ndA5FlatReferencePhysicalProfile B m branch Cband j E| ≤
        2 * ndA5ReferenceAbsorbBar B Cband * cap +
          14 * W * ndA5FlatReferenceNonproportionalError m Cfm1)

/-- For every admissible fixed tube constant, one conditioned-FM1 constant
works eventually for every branch, band, event, time, and both laws. -/
theorem exists_eventually_ndA5ReferenceTerminalAggregateBoundAt
    (Cband : ℝ) (hCband : (1 / 2 : ℝ) ≤ Cband) :
    ∃ Cfm1 : ℝ, 0 ≤ Cfm1 ∧
      ∀ᶠ B : ℕ in atTop,
        NDA5ReferenceTerminalAggregateBoundAt B Cband Cfm1 := by
  have hCpos : 0 < Cband := by positivity
  have hK : (1 : ℝ) ≤ (771 / 100 : ℝ) * Cband := by
    nlinarith
  obtain ⟨Cfm1, hCfm1, hFM1⟩ :=
    ndConditionedFM1Nat 11 (by norm_num)
      ((771 / 100 : ℝ) * Cband) hK
  refine ⟨Cfm1, hCfm1, ?_⟩
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [Tao.eventually_taoSection5AffineSourceScaleFacts,
      Tao.eventually_taoSection5PassLostWindowFacts,
      hlog.eventually_ge_atTop (300000 : ℝ),
      eventually_three_mul_ndA5TubeWidth_le_log Cband hCpos,
      eventually_ndA5ReferenceTerminalCellPacketAt Cband hCpos,
      eventually_ndA5PaddedBandWindow_diameter_le_m0 Cband hCband]
      with B facts lost hlogB hpadding hschedule hdiam
  rw [NDA5ReferenceTerminalAggregateBoundAt]
  intro branch j E hj
  exact
    abs_sum_ndA5TerminalAtomNominalIdealMass_sub_referenceProfiles_le
      facts lost hlogB hCband hpadding hj (hdiam branch j hj)
        hCfm1 hFM1 hschedule

end
end ND
end Erdos1135
