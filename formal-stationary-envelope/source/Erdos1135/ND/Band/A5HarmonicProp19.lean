/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Band.A5HarmonicResidue
import Erdos1135.Tao.Syracuse.Prop19

/-!
# Proposition 1.9 For One Exact Harmonic Band

This leaf applies the checked source-faithful Proposition 1.9 theorem to the
exact A5 harmonic band source.  It contains no FullGood event or prefix-tail
estimate.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Proposition 1.9 transfers the exact-band harmonic source-residue bound to
full valuation-list L1 at the Section 5 horizon. -/
theorem taoProp19ValuationTV_ndA5HarmonicBandPMF_le
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (j : ℕ) (hcount : 0 < ndA5BandCount B branch)
    (hM : 1 ≤ Tao.taoSection5NPrime B) :
    Tao.taoProp19ValuationTV
        (ndA5HarmonicBandPMF B branch j hB hcount)
        (Tao.taoSection5N0 B) ≤
      4 * ((2 : ℝ) ^
        (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ)))) := by
  have hscale :
      ((2 : ℝ) + 1) * (Tao.taoSection5N0 B : ℝ) ≤
        (Tao.taoSection5NPrime B : ℝ) := by
    norm_num [Tao.taoSection5NPrime]
  have hresidue :=
    taoTV_ndA5HarmonicBandPMF_sourceResidue_canonical_le
      hB j hcount hM
  have hvaluation :=
    Tao.taoProp19CanonicalApproximationWithConstants_checked
      (c0 := 1) (C0 := 2) (by norm_num) (by norm_num)
      (Tao.taoSection5N0 B) (Tao.taoSection5NPrime B) hscale
      (ndA5HarmonicBandPMF B branch j hB hcount)
      hresidue
  convert hvaluation using 1;
    norm_num [Tao.taoProp19DecayExponent_one]

end

end ND
end Erdos1135
