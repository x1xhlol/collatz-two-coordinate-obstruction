import Erdos1135.Tao.Section5.Schedule
import Erdos1135.Tao.Probability.LogWindowResidueRoom

/-!
# Section 5 Scheduled Residue Bound

This leaf applies the finite log-window room theorem to the common-threshold
Section 5 schedule.  It exposes the fixed full-L1 constant `C0 = 2` for an
arbitrary proof of positive source mass.
-/

namespace Erdos1135
namespace Tao

/-- The common Section 5 schedule supplies the canonical odd-residue estimate
with the fixed full-L1 constant `C0 = 2`. -/
theorem TaoSection5ResidueScheduleFacts.residue_le_two_rpow_neg
    {B : ℕ} (facts : TaoSection5ResidueScheduleFacts B)
    (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch))) :
    taoTV
        (taoProp19SourceResidueLaw
          (oddLogWindowOddNatPMF
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch)
            hmass)
          (taoSection5NPrime B))
        (taoCanonicalUniformOddResiduePMF (taoSection5NPrime B)) ≤
      2 * ((2 : ℝ) ^ (-(taoSection5NPrime B : ℝ))) :=
  taoTV_oddLogWindow_sourceResidue_canonical_le_two_rpow_neg
    (facts.one_le_lo branch) (facts.width branch) hmass
    facts.one_le_nPrime (facts.room branch)

end Tao
end Erdos1135
