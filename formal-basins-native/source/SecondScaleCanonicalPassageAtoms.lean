import SecondScaleBoundedPassageWords
import SecondScaleAtomWordBudget

set_option autoImplicit false
open Filter Topology

namespace CollatzPassageAtomsSecondScale
open Erdos1135SecondScale.Tao CollatzClockSecondScale

theorem canonical_bounded_word_bad_probability_le {B : ℕ}
    (hB : 1 < B) (hL : 100 ≤ Real.log (B : ℝ))
    (facts : TaoSection5LogWindowProp19Output B) (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass (oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))) :
    ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass).toOuterMeasure
      {q : TaoOddNat | q.1 ∉ boundedPassageWordEvent B (taoSection5N0 B) (atomWordBudget B)}).toReal ≤
        coarsePrefixError B := by
  let μ := oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have hE : 0 < Real.log (B : ℝ) / 1000 := by linarith
  have hTV : taoProp19ValuationTV μ (taoSection5N0 B) ≤
      4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) := facts.valuationBound branch
  apply source_event_bad_probability_le μ facts.schedule.one_le_n0 hE
    {q : TaoOddNat | q.1 ∈ boundedPassageWordEvent B (taoSection5N0 B) (atomWordBudget B)} hTV
  intro q hqs hgood
  have hmem := canonical_source_support_mem branch hmass q hqs
  have hq := canonical_window_threshold_lt hB hmem
  have hBp : 0 < B := by omega
  obtain ⟨τ, hτn, hfirst, _⟩ := exists_centered_first_hit_five hBp q.2 hq.le hE.le
    (canonical_clock_cost hBp) hgood
    (canonical_clock_upperIndex_le hBp hL hE.le le_rfl hmem)
  exact prefix_good_bounded_word q.2 hE.le hgood ⟨τ, hτn, hfirst⟩

/-- A bound uniform over every landing value, including the artificial atom
at one when first passage fails. -/
theorem canonical_passage_atom_finite_bound {B : ℕ}
    (hB : 1 < B) (hL : 100 ≤ Real.log (B : ℝ))
    (facts : TaoSection5LogWindowProp19Output B) (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass (oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))) (m : ℕ) :
    ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch) hmass).toOuterMeasure
      {q : TaoOddNat | (syracusePassLocationAtMostOrOne B q.1 hB.le).val = m}).toReal ≤
        coarsePrefixError B + 4 * (B : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have h0 := total_passage_atom_probability_le
    (n := taoSection5N0 B) (L := atomWordBudget B) hB.le hmass
    (fun q hq => (canonical_window_threshold_lt hB hq).le) m
  have h1 := canonical_bounded_word_bad_probability_le hB hL facts branch hmass
  have h2 := atomWordBudget_mass_le hB.le (facts.schedule.mass_lower branch)
  exact h0.trans (add_le_add h1 h2)

/-- Actual canonical first-passage laws have uniformly polynomially small
point masses on both full source windows. -/
theorem eventually_canonical_passage_atom_polynomial :
    ∀ᶠ B : ℕ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass (oddLogWindow
        (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)),
      ∀ hB : 1 ≤ B, ∀ m : ℕ,
      ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
        {q : TaoOddNat | (syracusePassLocationAtMostOrOne B q.1 hB).val = m}).toReal ≤
          5 * (B : ℝ) ^ (-(1 / 12800000 : ℝ)) := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog.eventually_ge_atTop 100,
    eventually_taoSection5LogWindowProp19Output, eventually_atom_total_error_le]
    with B hB hL facts herr
  intro branch hmass hB1 m
  exact (canonical_passage_atom_finite_bound hB hL facts branch hmass m).trans herr

end CollatzPassageAtomsSecondScale
