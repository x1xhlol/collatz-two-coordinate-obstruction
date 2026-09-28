import Erdos1135.ND.Band.A5BandPMF
import Erdos1135.ND.Band.A5TerminalAtomCoverageProbability

/-!
# Exact-Band A5 Terminal-Coverage Probabilities

This leaf specializes the one-time FullGood complement charge to laws mapped
from the exact finite A5 band carrier.  Support removes the redundant physical
band intersection.  The harmonic law keeps coefficient one; the flat law is
then dominated by the harmonic FullGood charge with the exact within-band
factor `exp beta`.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The strict FullGood failure charge for the flat law is dominated by the
harmonic failure charge with the within-band factor. -/
theorem ndA5FlatBandPMF_fullPrefixGoodComplMass_le_exp_mul_harmonic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) (C : ℝ) :
    ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal ≤
      Real.exp (ndA5BandBeta B branch) *
        ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5FullPrefixGoodEvent B C)ᶜ).toReal :=
  ndA5FlatBandPMF_eventMass_le_exp_mul_harmonic hB hcount _

/-- For any law mapped from the exact band carrier, the passage event needs
no explicit band intersection in its probability. -/
theorem abs_ndA5BandMappedPassMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {E : Set ℕ}
    (q : PMF (NDA5BandCarrier B branch j))
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
    |((q.map ndA5BandValueToOddNat).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal -
        ((q.map ndA5BandValueToOddNat).toOuterMeasure
          (ndA5TerminalAtomUnion B branch C j E)).toReal| ≤
      ((q.map ndA5BandValueToOddNat).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal := by
  have hcharge :=
    abs_ndA5PassBandMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
      (E := E) (q.map ndA5BandValueToOddNat) descent time lost hbudget hlogB
      hpadding hWn0 hWlarge hwidth hj
  rw [ndA5BandMappedPMF_toOuterMeasure_inter_band] at hcharge
  exact hcharge

/-- The exact harmonic band law pays the FullGood complement once. -/
theorem abs_ndA5HarmonicBandPassMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
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
      ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal := by
  simpa only [ndA5HarmonicBandPMF] using
    abs_ndA5BandMappedPassMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
      (ndA5HarmonicBandCarrierPMF B branch j hB hcount)
      descent time lost hbudget hlogB hpadding hWn0 hWlarge hwidth hj

/-- The exact flat band law is controlled by the same harmonic FullGood
charge, with only the within-band density-distortion factor. -/
theorem abs_ndA5FlatBandPassMass_sub_terminalAtomUnionMass_le_exp_mul_harmonicFullPrefixGoodCompl
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
        ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5FullPrefixGoodEvent B C)ᶜ).toReal := by
  calc
    |((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
          (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5TerminalAtomUnion B branch C j E)).toReal| ≤
      ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal := by
          simpa only [ndA5FlatBandPMF] using
            abs_ndA5BandMappedPassMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
              (ndA5FlatBandCarrierPMF B branch j hB hcount)
              descent time lost hbudget hlogB hpadding hWn0 hWlarge
              hwidth hj
    _ ≤ Real.exp (ndA5BandBeta B branch) *
        ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
          (ndA5FullPrefixGoodEvent B C)ᶜ).toReal :=
      ndA5FlatBandPMF_fullPrefixGoodComplMass_le_exp_mul_harmonic
        hB hcount C

end

end ND
end Erdos1135
