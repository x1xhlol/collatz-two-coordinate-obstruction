import CanonicalClockWindows
import CoarsePrefixProbabilityRate
import Erdos1135.Tao.Probability.LogWindowOddNatPoint

open Filter
open scoped Topology

namespace CollatzClockAudit
open Erdos1135.Tao

theorem canonical_source_support_mem {B : ℕ} (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass (oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)))
    (q : TaoOddNat)
    (hq : q ∈ (oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass).support) :
    q.1 ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch) := by
  by_contra hn
  exact (PMF.mem_support_iff _ q).mp hq
    (oddLogWindowOddNatPMF_apply_eq_zero_of_not_mem hmass q hn)

/-- The individual centered first-passage clock holds throughout both full
canonical windows on the already-proved closed typical event. -/
theorem eventually_canonical_centered_first_hit :
    ∀ᶠ B : ℕ in atTop, ∀ (branch : TaoSection5SourceBranch) (q : TaoOddNat),
      q.1 ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch) →
      taoSection5TypicalTuple B (taoSection5N0 B)
        (syracuseValuationPNatList (taoSection5N0 B) q.1 q.2) →
      q ∈ localClockGoodEvent B (taoSection5N0 B) (taoSection5TypicalSlack B) := by
  filter_upwards [eventually_canonical_clock_windows] with B hB
  intro branch q hmem htyp
  have hwin := hB.2.2 branch q.1 hmem
  exact section5_centered_first_hit (by omega) q.2 hwin.1.le hB.2.1 htyp hwin.2

/-- The sharp finite prefix-concentration error bounds failure of the actual
start-centered clock, including no-hit outcomes. -/
theorem eventually_canonical_clock_bad_probability_le :
    ∀ᶠ B : ℕ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass (oddLogWindow
        (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)),
      ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
        (localClockGoodEvent B (taoSection5N0 B) (taoSection5TypicalSlack B))ᶜ).toReal ≤
          localPrefixError B := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_canonical_clock_windows, eventually_taoSection5LogWindowProp19Output,
    hlog.eventually_gt_atTop 0] with B hwin facts hL
  intro branch hmass
  let μ := oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have hE : 0 < taoSection5TypicalSlack B := Real.rpow_pos_of_pos hL _
  have hTV : taoProp19ValuationTV μ (taoSection5N0 B) ≤
      4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) := facts.valuationBound branch
  apply source_event_bad_probability_le μ facts.schedule.one_le_n0 hE _ hTV
  intro q hqs hgood
  have hmem := canonical_source_support_mem branch hmass q hqs
  have hq := hwin.2.2 branch q.1 hmem
  exact exists_centered_first_hit_five (by omega) q.2 hq.1.le hE.le
    hwin.2.1 hgood hq.2

/-- With the coarser error `log B / 1000`, the actual first hit lands above
`sqrt B` except for the explicit finite Bernstein-plus-TV error. -/
theorem canonical_coarse_landing_bad_probability_le {B : ℕ}
    (hB : 1 < B) (hL : 100 ≤ Real.log (B : ℝ))
    (facts : TaoSection5LogWindowProp19Output B) (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass (oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))) :
    ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass).toOuterMeasure
      (largeLandingGoodEvent B (taoSection5N0 B))ᶜ).toReal ≤ coarsePrefixError B := by
  let μ := oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have hE : 0 < Real.log (B : ℝ) / 1000 := by linarith
  have hTV : taoProp19ValuationTV μ (taoSection5N0 B) ≤
      4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) := facts.valuationBound branch
  apply source_event_bad_probability_le μ facts.schedule.one_le_n0 hE _ hTV
  intro q hqs hgood
  have hmem := canonical_source_support_mem branch hmass q hqs
  have hq := canonical_window_threshold_lt hB hmem
  have hBp : 0 < B := by omega
  obtain ⟨τ, hτn, hfirst, _⟩ := exists_centered_first_hit_five hBp q.2 hq.le hE.le
    (canonical_clock_cost hBp) hgood
    (canonical_clock_upperIndex_le hBp hL hE.le le_rfl hmem)
  have hτpos : 0 < τ := by
    by_contra hz
    have hτ0 : τ = 0 := by omega
    have hh := hfirst.1
    simp [hτ0, not_le_of_gt hq] at hh
  exact ⟨τ, hτn, hfirst, first_hit_landing_gt_sqrt_of_prefix_bounds hBp q.2
    hτpos hτn hE.le le_rfl hL hfirst hgood⟩

/-- A polynomial failure bound for a genuine first hit whose odd landing is
above the square-root barrier; both canonical source branches are included. -/
theorem eventually_canonical_large_landing_polynomial :
    ∀ᶠ B : ℕ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass (oddLogWindow
        (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)),
      ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
        (largeLandingGoodEvent B (taoSection5N0 B))ᶜ).toReal ≤
          (B : ℝ) ^ (-(1 / 12800000 : ℝ)) := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog.eventually_ge_atTop 100,
    eventually_taoSection5LogWindowProp19Output, eventually_coarsePrefixError_le_rpow]
    with B hB hL facts herr
  intro branch hmass
  exact (canonical_coarse_landing_bad_probability_le hB hL facts branch hmass).trans herr

end CollatzClockAudit

#print axioms CollatzClockAudit.canonical_source_support_mem
#print axioms CollatzClockAudit.eventually_canonical_centered_first_hit
#print axioms CollatzClockAudit.eventually_canonical_clock_bad_probability_le
#print axioms CollatzClockAudit.canonical_coarse_landing_bad_probability_le
#print axioms CollatzClockAudit.eventually_canonical_large_landing_polynomial
