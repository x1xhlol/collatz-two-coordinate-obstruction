import Erdos1135.ND.Band.A5BandCoverageFullGood
import Erdos1135.ND.Band.A5HarmonicFullGoodRate
import Erdos1135.ND.Discrepancy.A5TwoProfileFlat

/-!
# A5 Band-Coverage Rate Consumers

This high integration leaf feeds the checked scalar FullGood rate into the
exact harmonic and flat terminal-coverage consumers.  The harmonic endpoint
uses one quarter of the power-ten budget.  The flat endpoint is strict because
the existing actual-band distortion bound is strictly below four.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Uniform eventual harmonic passage/terminal coverage at one quarter of
the frozen power-ten logarithmic budget. -/
theorem eventually_abs_ndA5HarmonicBandPassMass_sub_terminalAtomUnionMass_le_quarter_log_rpow_neg_ten
    (C : ℝ) (hC : (40 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ)
        (hB : 1 ≤ B)
        (hcount : 0 < ndA5BandCount B branch)
        (descent : Tao.TaoSection5DescentScaleFacts B)
        (time : Tao.TaoSection5PassTimeLocalizationFacts B)
        (lost : Tao.TaoSection5PassLostWindowFacts B)
        (hbudget : Tao.taoSection5ReversePrefixScalarBudget B)
        (hlogB : (300000 : ℝ) ≤ Real.log (B : ℝ))
        (hpadding : 3 * ndA5TubeWidth B C ≤
          (33 / 500000 : ℝ) * Real.log (B : ℝ))
        (hWn0 : 10 * ndA5TubeWidth B C ≤
          (Tao.taoSection5N0 B : ℝ))
        (hWlarge : 6 ≤ ndA5TubeWidth B C)
        (hwidth : ndA5TubeWidth B C ≤
          Tao.taoSection5TypicalSlack B)
        (hj : j < ndA5BandCount B branch),
        |((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal -
            ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
              (ndA5TerminalAtomUnion B branch C j E)).toReal| ≤
          (1 / 4 : ℝ) *
            Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by
  filter_upwards
      [eventually_ndA5HarmonicFullGoodEnvelope_le_quarter_log_rpow_neg_ten
        C hC]
    with B hrate
  intro branch j E hB hcount descent time lost hbudget hlogB
    hpadding hWn0 hWlarge hwidth hj
  have hcoverage :=
    abs_ndA5HarmonicBandPassMass_sub_terminalAtomUnionMass_le_fullGoodEnvelope
      (B := B) (branch := branch) (j := j) (C := C) (E := E)
      hB hcount descent time lost hbudget hlogB
      hpadding hWn0 hWlarge hwidth hj
  exact hcoverage.trans hrate

/-- Uniform eventual flat passage/terminal coverage at the strict full
power-ten logarithmic budget. -/
theorem eventually_abs_ndA5FlatBandPassMass_sub_terminalAtomUnionMass_lt_log_rpow_neg_ten
    (C : ℝ) (hC : (40 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ)
        (hB : 1 ≤ B)
        (hcount : 0 < ndA5BandCount B branch)
        (descent : Tao.TaoSection5DescentScaleFacts B)
        (time : Tao.TaoSection5PassTimeLocalizationFacts B)
        (lost : Tao.TaoSection5PassLostWindowFacts B)
        (hbudget : Tao.taoSection5ReversePrefixScalarBudget B)
        (hlogB : (300000 : ℝ) ≤ Real.log (B : ℝ))
        (hpadding : 3 * ndA5TubeWidth B C ≤
          (33 / 500000 : ℝ) * Real.log (B : ℝ))
        (hWn0 : 10 * ndA5TubeWidth B C ≤
          (Tao.taoSection5N0 B : ℝ))
        (hWlarge : 6 ≤ ndA5TubeWidth B C)
        (hwidth : ndA5TubeWidth B C ≤
          Tao.taoSection5TypicalSlack B)
        (hj : j < ndA5BandCount B branch),
        |((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
              (Tao.taoSection5PassEvent B E)).toReal -
            ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
              (ndA5TerminalAtomUnion B branch C j E)).toReal| <
          Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by
  filter_upwards
      [eventually_ndA5HarmonicFullGoodEnvelope_le_quarter_log_rpow_neg_ten
        C hC]
    with B hrate
  intro branch j E hB hcount descent time lost hbudget hlogB
    hpadding hWn0 hWlarge hwidth hj
  have hcoverage :=
    abs_ndA5FlatBandPassMass_sub_terminalAtomUnionMass_le_exp_mul_fullGoodEnvelope
      (B := B) (branch := branch) (j := j) (C := C) (E := E)
      hB hcount descent time lost hbudget hlogB
      hpadding hWn0 hWlarge hwidth hj
  have hlogPos : 0 < Real.log (B : ℝ) := by
    linarith
  have hrpowPos :
      0 < Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) :=
    Real.rpow_pos_of_pos hlogPos _
  have hquarterPos :
      0 < (1 / 4 : ℝ) *
        Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) :=
    mul_pos (by norm_num) hrpowPos
  calc
    |((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5TerminalAtomUnion B branch C j E)).toReal| ≤
        Real.exp (ndA5BandBeta B branch) *
          (2 * (Tao.taoSection5N0 B : ℝ) *
              Real.exp
                (-min
                  ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
                    (32 * (Tao.taoSection5N0 B : ℝ)))
                  ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) +
            4 * (2 : ℝ) ^
              (-((1 / 128 : ℝ) *
                (Tao.taoSection5N0 B : ℝ)))) := hcoverage
    _ ≤ Real.exp (ndA5BandBeta B branch) *
        ((1 / 4 : ℝ) *
          Real.rpow (Real.log (B : ℝ)) (-10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hrate (Real.exp_pos _).le
    _ < 4 * ((1 / 4 : ℝ) *
        Real.rpow (Real.log (B : ℝ)) (-10 : ℝ)) :=
      mul_lt_mul_of_pos_right
        (exp_ndA5BandBeta_lt_four (branch := branch) hB hlogB)
        hquarterPos
    _ = Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by ring

end

end ND
end Erdos1135
