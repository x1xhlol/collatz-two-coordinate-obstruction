import Erdos1135.Tao.Section5.PassTypicalFailure

open Filter
open scoped Topology

namespace CollatzClockAudit

open Erdos1135 Tao

/-- The sharp finite error, before weakening it to a power of the logarithm. -/
noncomputable def localPrefixError (B : ℕ) : ℝ :=
  (taoSection5N0 B : ℝ) * (2 * Real.exp
    (-min ((taoSection5TypicalSlack B) ^ 2 / (32 * (taoSection5N0 B : ℝ)))
      (taoSection5TypicalSlack B / 8))) +
    4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ)))

theorem actual_prefix_bad_probability_le
    (μ : PMF TaoOddNat) {n : ℕ} (hn : 0 < n)
    {E err : ℝ} (hE : 0 < E)
    (hTV : taoProp19ValuationTV μ n ≤ err) :
    ((taoProp19ActualValuationLaw μ n).toOuterMeasure
      (taoGeom2PrefixBadEvent E n)).toReal ≤
        (n : ℝ) * (2 * Real.exp (-min (E ^ 2 / (32 * (n : ℝ))) (E / 8))) + err := by
  have ht := pmfOuterMass_le_add_of_taoPMFFullL1_le
    (p := taoProp19ActualValuationLaw μ n) (q := geom2PNatListPMF n)
    (E := taoGeom2PrefixBadEvent E n) hTV
  exact ht.trans (add_le_add (geom2PNatListPMF_prefixBad_le_nat_mul hn hE) le_rfl)

theorem canonical_source_prefix_bad_probability_le
    {B : ℕ} (facts : TaoSection5LogWindowProp19Output B)
    (hE : 0 < taoSection5TypicalSlack B) (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass (oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))) :
    ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass).toOuterMeasure
      (taoSection5ClosedGoodEvent B)ᶜ).toReal ≤ localPrefixError B := by
  let μ := oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have hval : taoProp19ValuationTV μ (taoSection5N0 B) ≤
      4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) :=
    facts.valuationBound branch
  have h := actual_prefix_bad_probability_le μ facts.schedule.one_le_n0 hE hval
  change ((taoProp19ActualValuationLaw μ (taoSection5N0 B)).toOuterMeasure
    (taoSection5ClosedPrefixBadEvent B)).toReal ≤ localPrefixError B at h
  rw [taoProp19ActualValuationLaw_closedPrefixBad B μ hE] at h
  exact h

theorem eventually_canonical_source_prefix_bad_probability_le :
    ∀ᶠ B : ℕ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass (oddLogWindow
        (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)),
      ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
        (taoSection5ClosedGoodEvent B)ᶜ).toReal ≤ localPrefixError B := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_taoSection5LogWindowProp19Output,
    hlog.eventually_gt_atTop 0] with B facts hB
  intro branch hmass
  exact canonical_source_prefix_bad_probability_le facts
    (Real.rpow_pos_of_pos hB _) branch hmass

#print axioms actual_prefix_bad_probability_le
#print axioms canonical_source_prefix_bad_probability_le
#print axioms eventually_canonical_source_prefix_bad_probability_le

end CollatzClockAudit
