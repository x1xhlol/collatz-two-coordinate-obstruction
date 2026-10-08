import Erdos1135.ND.Band.A5TwoProfilePhysicalZeroExtension
import Erdos1135.ND.Discrepancy.A5TwoProfileA6

/-!
# A5 two-profile A6 on the original physical window

The checked A6 theorem is stated on the union of the base and first-shift
intrinsic tubes.  This leaf transports it to the original endpoint-indexed
physical window using the zero-extension equalities.  No endpoint is split or
replaced, and the two profile errors remain separate.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- Reciprocal two-profile sum on the original positive physical window. -/
def ndA5ReciprocalTwoProfilePhysicalSum
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M : ℝ) : ℝ :=
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
    ∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandRawQTerm B branch A W nu r

/-- Flat two-profile sum on the same original physical window. -/
def ndA5FlatTwoProfilePhysicalSum
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M : ℝ) : ℝ :=
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  ∑ nu ∈ ndA5PhysicalNuWindow B branch C j,
    ∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandFlatRawQTerm B branch A W nu r

/-- Exact reciprocal raw A6 error before band normalization. -/
def ndA5ReciprocalTwoProfileA6Error
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M EA6 c kappa : ℝ) : ℝ :=
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let Z0 := ndA5TubeRawMass A W
  Z0 *
      (ndEndpointDbar c kappa I0.card *
        (64 * (I0.card : ℝ) * W / (ndA5TubeLo A W : ℝ))) +
    (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
      24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) +
    (ndA5BandBeta B branch / Real.log 2) * EA6

/-- Exact flat raw A6 error before band normalization. -/
def ndA5FlatTwoProfileA6Error
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (M EA6 c kappa : ℝ) : ℝ :=
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let Z0 := ndA5TubeRawMass A W
  let beta := ndA5BandBeta B branch
  Z0 *
      ((2 * Real.exp beta - 1) *
        ndEndpointDbar c kappa I0.card *
          (64 * (I0.card : ℝ) * W / (ndA5TubeLo A W : ℝ))) +
    Real.exp beta *
      (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
        24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) +
    ndA5FlatPhaseMean beta * EA6

/-- The reciprocal A6 center transported to the original physical window. -/
theorem
    abs_ndA5ReciprocalTwoProfilePhysicalSum_sub_beta_div_logFourThirds_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M EA6 c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch)
    (hA6 :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤ EA6) :
    |ndA5ReciprocalTwoProfilePhysicalSum B branch C j M -
        ndA5BandBeta B branch / ndA5LogFourThirds| ≤
      ndA5ReciprocalTwoProfileA6Error B branch C j M EA6 c kappa := by
  have hTube0 : NDA5InteriorTubeFacts B j branch C M :=
    ndA5InteriorTubeFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
  have hTube1 : NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1) :=
    ndA5AnalyticTubeFacts_add_one_of_sourceGuards
      hB hlogB hC hM hpadding hshift hj
  have hraw :=
    abs_sum_ndA5NominalStrictBandRawQ_sub_beta_div_logFourThirds_le_of_interior
      hPhase hB hlogB hTube0 hTube1 hA6
  have hzero :=
    sum_ndA5NominalStrictBandRawQ_physicalNuWindow_eq_fullTube_union_of_sourceGuards
      hB hlogB hC hM hpadding hshift hj
  rw [ndA5ReciprocalTwoProfilePhysicalSum, hzero]
  simpa only [ndA5ReciprocalTwoProfileA6Error] using hraw

/-- The flat A6 center transported to the same original physical window. -/
theorem
    abs_ndA5FlatTwoProfilePhysicalSum_sub_exp_sub_one_div_logFourThirds_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C M EA6 c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch)
    (hA6 :
      |ndA5BandRawMass B branch C j M - 1 / ndA5PhaseDelta| ≤ EA6) :
    |ndA5FlatTwoProfilePhysicalSum B branch C j M -
        (Real.exp (ndA5BandBeta B branch) - 1) /
          ndA5LogFourThirds| ≤
      ndA5FlatTwoProfileA6Error B branch C j M EA6 c kappa := by
  have hTube0 : NDA5InteriorTubeFacts B j branch C M :=
    ndA5InteriorTubeFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
  have hTube1 : NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1) :=
    ndA5AnalyticTubeFacts_add_one_of_sourceGuards
      hB hlogB hC hM hpadding hshift hj
  have hraw :=
    abs_sum_ndA5NominalStrictBandFlatRawQ_sub_exp_sub_one_div_logFourThirds_le_of_interior
      hPhase hB hlogB hTube0 hTube1 hA6
  have hzero :=
    sum_ndA5NominalStrictBandFlatRawQ_physicalNuWindow_eq_fullTube_union_of_sourceGuards
      hB hlogB hC hM hpadding hshift hj
  rw [ndA5FlatTwoProfilePhysicalSum, hzero]
  simpa only [ndA5FlatTwoProfileA6Error] using hraw

/-- Named eventual physical-window A6 packet at one base. -/
def NDA5TwoProfilePhysicalA6At
    (B : ℕ) (C c kappa : ℝ) : Prop :=
  ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
    j < ndA5BandCount B branch →
      ∀ M : ℝ, 0 < M →
        |ndA5InteriorShift B M| ≤
            (4 / 25 : ℝ) * ndA5TubeWidth B C →
          let EA6 := 3650000 * (C + C ^ 3) * ndA6PhysicalRate B
          (|ndA5ReciprocalTwoProfilePhysicalSum B branch C j M -
                ndA5BandBeta B branch / ndA5LogFourThirds| ≤
              ndA5ReciprocalTwoProfileA6Error
                B branch C j M EA6 c kappa) ∧
            (|ndA5FlatTwoProfilePhysicalSum B branch C j M -
                (Real.exp (ndA5BandBeta B branch) - 1) /
                  ndA5LogFourThirds| ≤
              ndA5FlatTwoProfileA6Error
                B branch C j M EA6 c kappa)

/-- Fixed-`C` physical-window A6 packet for every later original interior
endpoint. -/
theorem eventually_ndA5TwoProfilePhysicalA6
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C)
    {c kappa : ℝ} (hPhase : PhaseGap c kappa) :
    ∀ᶠ B : ℕ in Filter.atTop,
      NDA5TwoProfilePhysicalA6At B C c kappa := by
  have hCpos : 0 < C := by linarith
  have hlog : ∀ᶠ B : ℕ in Filter.atTop,
      (300000 : ℝ) ≤ Real.log B :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto
        (fun B : ℕ => (B : ℝ)) Filter.atTop Filter.atTop)).eventually_ge_atTop
          300000
  filter_upwards
    [Filter.eventually_ge_atTop (1 : ℕ), hlog,
      eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
      eventually_a6PhysicalInterior C hC]
      with B hB hlogB hpadding hA6
  rw [NDA5TwoProfilePhysicalA6At]
  intro branch j hj M hM hshift
  dsimp only
  have hA6' := hA6 branch j hj M hM hshift
  exact
    ⟨abs_ndA5ReciprocalTwoProfilePhysicalSum_sub_beta_div_logFourThirds_le
        hPhase hB hlogB hC hM hpadding hshift hj hA6',
      abs_ndA5FlatTwoProfilePhysicalSum_sub_exp_sub_one_div_logFourThirds_le
        hPhase hB hlogB hC hM hpadding hshift hj hA6'⟩

end
end ND
end Erdos1135
