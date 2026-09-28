import Erdos1135.ND.Band.A5BandCoverageProbability
import Erdos1135.ND.Band.A5HarmonicFullGood

/-!
# Quantitative FullGood Charge For Exact-Band Coverage

This integration leaf composes the exact flat and harmonic terminal-coverage
consumers with the checked harmonic FullGood-complement envelope.  It performs
no scalar rate absorption and introduces no flat valuation-TV estimate.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The exact harmonic passage/terminal discrepancy is bounded by the
positive-prefix tail plus the Proposition 1.9 valuation error. -/
theorem abs_ndA5HarmonicBandPassMass_sub_terminalAtomUnionMass_le_fullGoodEnvelope
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {E : Set ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (descent : Tao.TaoSection5DescentScaleFacts B)
    (time : Tao.TaoSection5PassTimeLocalizationFacts B)
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hbudget : Tao.taoSection5ReversePrefixScalarBudget B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hWn0 : 10 * ndA5TubeWidth B C ≤
      (Tao.taoSection5N0 B : ℝ))
    (hWlarge : 6 ≤ ndA5TubeWidth B C)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hj : j < ndA5BandCount B branch) :
    |((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5TerminalAtomUnion B branch C j E)).toReal| ≤
      2 * (Tao.taoSection5N0 B : ℝ) *
        Real.exp
          (-min
            ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
              (32 * (Tao.taoSection5N0 B : ℝ)))
            ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) +
      4 * (2 : ℝ) ^
        (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) := by
  have hcoverage :=
    abs_ndA5HarmonicBandPassMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
      (C := C) (E := E) hB hcount descent time lost hbudget hlogB
      hpadding hWn0 hWlarge hwidth hj
  exact hcoverage.trans
    (ndA5HarmonicBandPMF_fullPrefixGoodComplMass_le
      (B := B) (branch := branch) (j := j) (C := C)
      hB hcount hWlarge)

/-- The exact flat passage/terminal discrepancy is bounded by the same
harmonic envelope, multiplied only by the within-band density distortion. -/
theorem abs_ndA5FlatBandPassMass_sub_terminalAtomUnionMass_le_exp_mul_fullGoodEnvelope
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {E : Set ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (descent : Tao.TaoSection5DescentScaleFacts B)
    (time : Tao.TaoSection5PassTimeLocalizationFacts B)
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hbudget : Tao.taoSection5ReversePrefixScalarBudget B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hWn0 : 10 * ndA5TubeWidth B C ≤
      (Tao.taoSection5N0 B : ℝ))
    (hWlarge : 6 ≤ ndA5TubeWidth B C)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hj : j < ndA5BandCount B branch) :
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
          (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ)))) := by
  have hcoverage :=
    abs_ndA5FlatBandPassMass_sub_terminalAtomUnionMass_le_exp_mul_harmonicFullPrefixGoodCompl
      (C := C) (E := E) hB hcount descent time lost hbudget hlogB
      hpadding hWn0 hWlarge hwidth hj
  have hfull :=
    ndA5HarmonicBandPMF_fullPrefixGoodComplMass_le
      (B := B) (branch := branch) (j := j) (C := C)
      hB hcount hWlarge
  exact hcoverage.trans
    (mul_le_mul_of_nonneg_left hfull
      (Real.exp_pos (ndA5BandBeta B branch)).le)

end

end ND
end Erdos1135
