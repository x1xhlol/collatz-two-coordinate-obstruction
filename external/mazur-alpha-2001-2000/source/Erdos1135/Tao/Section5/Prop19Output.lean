import Erdos1135.Tao.Section5.ScheduleResidue
import Erdos1135.Tao.Syracuse.Prop19

/-!
# Section 5 Proposition 1.9 Output

This leaf instantiates Proposition 1.9 on Tao's common-threshold Section 5
schedule.  It stores the actual branchwise residue and valuation conclusions
with the shared constants `C0 = 2`, `c1 = 1 / 128`, and `C1 = 4`.  It does not
import the Section 5 facade or claim the later no-hit estimate.
-/

namespace Erdos1135
namespace Tao

open Filter

/-- The actual Proposition 1.9 inputs and output at one common threshold `B`.
Only the source branch varies; the threshold and both exponents are shared. -/
structure TaoSection5LogWindowProp19Output (B : ℕ) : Prop where
  schedule : TaoSection5ResidueScheduleFacts B
  residueBound : ∀ branch : TaoSection5SourceBranch,
    taoTV
        (taoProp19SourceResidueLaw
          (oddLogWindowOddNatPMF
            (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch)
            (schedule.mass_pos branch))
          (taoSection5NPrime B))
        (taoCanonicalUniformOddResiduePMF (taoSection5NPrime B)) ≤
      2 * ((2 : ℝ) ^ (-(taoSection5NPrime B : ℝ)))
  valuationBound : ∀ branch : TaoSection5SourceBranch,
    taoProp19ValuationTV
        (oddLogWindowOddNatPMF
          (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch)
          (schedule.mass_pos branch))
        (taoSection5N0 B) ≤
      4 * ((2 : ℝ) ^
        (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))))

/-- The common schedule's quadratic room supplies the residue input, and the
checked explicit Proposition 1.9 theorem supplies the valuation output. -/
theorem TaoSection5LogWindowProp19Output.of_schedule
    {B : ℕ} (facts : TaoSection5ResidueScheduleFacts B) :
    TaoSection5LogWindowProp19Output B := by
  have hresidue (branch : TaoSection5SourceBranch) :
      taoTV
          (taoProp19SourceResidueLaw
            (oddLogWindowOddNatPMF
              (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch)
              (facts.mass_pos branch))
            (taoSection5NPrime B))
          (taoCanonicalUniformOddResiduePMF (taoSection5NPrime B)) ≤
        2 * ((2 : ℝ) ^ (-(taoSection5NPrime B : ℝ))) :=
    facts.residue_le_two_rpow_neg branch (facts.mass_pos branch)
  refine
    { schedule := facts
      residueBound := hresidue
      valuationBound := ?_ }
  intro branch
  have hscale :
      ((2 : ℝ) + 1) * (taoSection5N0 B : ℝ) ≤
        (taoSection5NPrime B : ℝ) := by
    norm_num [taoSection5NPrime]
  have hvaluation :=
    taoProp19CanonicalApproximationWithConstants_checked
      (c0 := 1) (C0 := 2) (by norm_num) (by norm_num)
      (taoSection5N0 B) (taoSection5NPrime B) hscale
      (oddLogWindowOddNatPMF
        (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch)
        (facts.mass_pos branch))
      (hresidue branch)
  convert hvaluation using 1 <;> norm_num [taoProp19DecayExponent_one]

/-- For all sufficiently large common thresholds, both Section 5 branches
carry the actual fixed-constant Proposition 1.9 output. -/
theorem eventually_taoSection5LogWindowProp19Output :
    ∀ᶠ B : ℕ in atTop, TaoSection5LogWindowProp19Output B :=
  eventually_taoSection5ResidueScheduleFacts.mono fun _ facts =>
    TaoSection5LogWindowProp19Output.of_schedule facts

end Tao
end Erdos1135
