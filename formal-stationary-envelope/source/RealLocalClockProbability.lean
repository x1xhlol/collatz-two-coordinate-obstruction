import RealClockFloorGeometry

open Filter
open scoped Topology

namespace CollatzClockAudit
open Erdos1135.Tao

theorem pmf_outer_probability_mono_support {α : Type*} (μ : PMF α) {S T : Set α}
    (h : S ∩ μ.support ⊆ T) :
    (μ.toOuterMeasure S).toReal ≤ (μ.toOuterMeasure T).toReal := by
  apply ENNReal.toReal_mono _ (μ.toOuterMeasure_mono h)
  apply ne_of_lt
  calc
    μ.toOuterMeasure T ≤ μ.toOuterMeasure Set.univ := μ.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
    _ < ⊤ := ENNReal.one_lt_top

theorem eventually_natural_clock_bad_log_power :
    ∀ᶠ B : ℕ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass (oddLogWindow
        (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)),
      ((oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch) hmass).toOuterMeasure
        (localClockGoodEvent B (taoSection5N0 B) (taoSection5TypicalSlack B))ᶜ).toReal ≤
          2 * (Real.log (B : ℝ)) ^ (-(1 / 10 : ℝ)) := by
  filter_upwards [eventually_canonical_centered_first_hit,
    eventually_taoSection5PassTypicalFailureFacts] with B hclock facts
  intro branch hmass
  let μ := oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) hmass
  have hmono : (μ.toOuterMeasure
      (localClockGoodEvent B (taoSection5N0 B) (taoSection5TypicalSlack B))ᶜ).toReal ≤
      (μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal := by
    apply pmf_outer_probability_mono_support
    intro q hq
    exact fun hc => hq.1 (hclock branch q (canonical_source_support_mem branch hmass q hq.2) hc)
  apply hmono.trans
  simpa only [μ, taoSection5PowerInteriorDelta, neg_div] using facts.closedGood_compl_le branch

theorem real_clock_bad_probability_le_floor_add {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (hx : 2 ≤ x) (hlog : 1 ≤ Real.log x)
    (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) :
    ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
      hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
      ((oddLogWindowOddNatPMF (taoSection5SourceLo (Nat.floor x) branch)
        (taoSection5SourceHi (Nat.floor x) branch)
        (floor_clock_source_mass_pos facts branch)).toOuterMeasure
        (localClockGoodEvent (Nat.floor x) (taoSection5N0 (Nat.floor x))
          (taoSection5TypicalSlack (Nat.floor x)))ᶜ).toReal +
        taoProp111FloorSourceError (Nat.floor x) := by
  apply (real_source_event_probability_le_floor_add facts branch hmass _).trans
  apply add_le_add _ le_rfl
  apply pmf_outer_probability_mono_support
  intro q hq
  exact fun hg => hq.1 (localClockGoodEvent_floor_subset_real hx hlog hg)

theorem eventually_real_clock_bad_probability_sharp :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
          localPrefixError (Nat.floor x) + taoProp111FloorSourceError (Nat.floor x) := by
  have hf : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  filter_upwards [eventually_taoProp111RealFloorWindowMassFacts, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    hf.eventually eventually_canonical_clock_bad_probability_le] with x facts hx hlog hnat
  intro branch hmass
  exact (real_clock_bad_probability_le_floor_add facts hx hlog branch hmass).trans
    (add_le_add (hnat branch (floor_clock_source_mass_pos facts branch)) le_rfl)

theorem eventually_real_clock_bad_probability_floor_log_power :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
          2 * (Real.log ((Nat.floor x : ℕ) : ℝ)) ^ (-(1 / 10 : ℝ)) +
            taoProp111FloorSourceError (Nat.floor x) := by
  have hf : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  filter_upwards [eventually_taoProp111RealFloorWindowMassFacts, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    hf.eventually eventually_natural_clock_bad_log_power] with x facts hx hlog hnat
  intro branch hmass
  exact (real_clock_bad_probability_le_floor_add facts hx hlog branch hmass).trans
    (add_le_add (hnat branch (floor_clock_source_mass_pos facts branch)) le_rfl)

theorem real_landing_bad_probability_le_floor_add {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x)
    (prop19 : TaoSection5LogWindowProp19Output (Nat.floor x)) (hx : 2 ≤ x)
    (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch))) :
    ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
      hmass).toOuterMeasure (realLargeLandingGoodEvent x)ᶜ).toReal ≤
        coarsePrefixError (Nat.floor x) + taoProp111FloorSourceError (Nat.floor x) := by
  apply (real_source_event_probability_le_floor_add facts branch hmass _).trans
  apply add_le_add _ le_rfl
  let B := Nat.floor x
  let μ := oddLogWindowOddNatPMF (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch) (floor_clock_source_mass_pos facts branch)
  have hB : 1 < B := by
    exact_mod_cast (Real.log_pos_iff (Nat.cast_nonneg (Nat.floor x))).mp facts.log_floor_pos
  have hBp : 0 < B := by omega
  have hL : 100 ≤ Real.log (B : ℝ) := by linarith [facts.log_floor_large]
  have hE : 0 < Real.log (B : ℝ) / 1000 := by linarith
  have hTV : taoProp19ValuationTV μ (taoSection5N0 B) ≤
      4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) := prop19.valuationBound branch
  apply source_event_bad_probability_le μ prop19.schedule.one_le_n0 hE _ hTV
  intro q hqs hgood
  have hmem := canonical_source_support_mem branch (floor_clock_source_mass_pos facts branch) q hqs
  have hq := canonical_window_threshold_lt hB hmem
  obtain ⟨τ, hτn, hfirst, _⟩ := exists_centered_first_hit_five hBp q.2 hq.le hE.le
    (canonical_clock_cost hBp) hgood
    (canonical_clock_upperIndex_le hBp hL hE.le le_rfl hmem)
  have hτpos : 0 < τ := by
    by_contra hz
    have hτ0 : τ = 0 := by omega
    have hh := hfirst.1
    simp [hτ0, not_le_of_gt hq] at hh
  refine ⟨τ, (syracuseFirstHitAtMostReal_iff_floor (by linarith : 0 ≤ x)).2 hfirst, ?_⟩
  exact real_landing_gt_sqrt_of_coarse_prefix hx hL q.2 hτpos hτn hfirst hgood

theorem eventually_real_landing_bad_probability_floor_power :
    ∀ᶠ x : ℝ in atTop, ∀ branch : TaoSection5SourceBranch,
      ∀ hmass : 0 < logFinsetMass
        (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)),
      ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
        hmass).toOuterMeasure (realLargeLandingGoodEvent x)ᶜ).toReal ≤
          ((Nat.floor x : ℕ) : ℝ) ^ (-(1 / 12800000 : ℝ)) +
            taoProp111FloorSourceError (Nat.floor x) := by
  have hf : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop := tendsto_nat_floor_atTop
  filter_upwards [eventually_taoProp111RealFloorWindowMassFacts, eventually_ge_atTop (2 : ℝ),
    hf.eventually eventually_taoSection5LogWindowProp19Output,
    hf.eventually eventually_coarsePrefixError_le_rpow] with x facts hx prop19 herr
  intro branch hmass
  exact (real_landing_bad_probability_le_floor_add facts prop19 hx branch hmass).trans
    (add_le_add herr le_rfl)

end CollatzClockAudit

#print axioms CollatzClockAudit.pmf_outer_probability_mono_support
#print axioms CollatzClockAudit.eventually_natural_clock_bad_log_power
#print axioms CollatzClockAudit.real_clock_bad_probability_le_floor_add
#print axioms CollatzClockAudit.eventually_real_clock_bad_probability_sharp
#print axioms CollatzClockAudit.eventually_real_clock_bad_probability_floor_log_power
#print axioms CollatzClockAudit.real_landing_bad_probability_le_floor_add
#print axioms CollatzClockAudit.eventually_real_landing_bad_probability_floor_power
