import Erdos1135.ND.Band.A5TerminalAtomCoverage
import Erdos1135.ND.Probability.ComplementCharge

/-!
# A5 Terminal-Atom Coverage: One-Time Complement Charge

This leaf applies the neutral coefficient-one PMF comparison to the checked
FullGood-gated terminal-atom identity.  Estimating the rejected FullGood mass
and evaluating or summing terminal-atom masses remain downstream steps.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The genuine band-passage mass and unrestricted terminal-atom-union mass
differ by at most the FullGood complement, charged once. -/
theorem abs_ndA5PassBandMass_sub_terminalAtomUnionMass_le_fullPrefixGoodCompl
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {E : Set ℕ}
    (p : PMF Tao.TaoOddNat)
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
    |(p.toOuterMeasure
          (Tao.taoSection5PassEvent B E ∩
            {N | N.1 ∈ ndA5OddBand B branch j})).toReal -
        (p.toOuterMeasure
          (ndA5TerminalAtomUnion B branch C j E)).toReal| ≤
      (p.toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal :=
  abs_pmfOuterMass_sub_le_compl_of_inter_eq p
    (ndA5PassBand_inter_fullPrefixGood_eq_terminalAtomUnion_inter
      descent time lost hbudget hlogB hpadding hWn0 hWlarge hwidth hj)

end

end ND
end Erdos1135
