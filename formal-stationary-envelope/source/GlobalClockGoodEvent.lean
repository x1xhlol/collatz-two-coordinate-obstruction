import ClockScaleStageEvent
import DefaultLandingStageClock
import GeometricClockAccumulation

open scoped BigOperators

namespace CollatzClockAudit
open Erdos1135.Tao

def globalClockGoodEvent (M : ℝ) (hM : 1 ≤ M) (j : ℕ) : Set TaoOddNat :=
  {q | q ∈ realLocalClockGoodEvent (clockScale M j) ∧
    (∀ i < j, (syracusePassLocationRealFloorOrOne (clockScale M (i + 1)) q.1
      (one_le_clockScale hM (i + 1))).1 ∈
        stageClockGoodEvent (clockScale M (i + 1)) (clockScale M i)) ∧
    M ^ (1 / 2 : ℝ) < (syracusePassLocationRealFloorOrOne M q.1 hM).1}

noncomputable def globalClockFailureBudget (C c M : ℝ) (j : ℕ) : ℝ :=
  200000 * (Real.log (clockScale M j)) ^ (-(1 / 10 : ℝ)) +
    (∑ i ∈ Finset.range j,
      (400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) +
        ∑ r ∈ Finset.Ico (i + 1) j, C * (Real.log (clockScale M r)) ^ (-c))) +
    (200000 * M ^ (-(1 / 12800000 : ℝ)) +
      ∑ r ∈ Finset.range j, C * (Real.log (clockScale M r)) ^ (-c))

theorem real_pass_value_congr {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x = y) (q : ℕ) :
    (syracusePassLocationRealFloorOrOne x q hx).1 =
      (syracusePassLocationRealFloorOrOne y q hy).1 := by
  subst y
  rfl

theorem reference_passage_small_landing_probability {C c x : ℝ}
    (facts : RealClockScaleFacts C c x)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha))) :
    pmfProb (realClockPassageLaw x facts.one_le_x .alpha hmass)
      {u | ¬ x ^ (1 / 2 : ℝ) < (u.1 : ℝ)} ≤
        200000 * x ^ (-(1 / 12800000 : ℝ)) := by
  rw [pmfProb_eq_toOuterMeasure_toReal, ← real_odd_source_map_passage_eq,
    PMF.toOuterMeasure_map_apply]
  apply le_trans ?_ (facts.landing_bound .alpha hmass)
  apply pmf_outer_probability_mono_support
  intro q hq hgood
  obtain ⟨τ, hτ, hland⟩ := hgood
  exact hq.1 (by simpa only [real_pass_value_eq_of_first_hit facts.one_le_x hτ] using hland)

theorem clock_ladder_top_source_small_landing {M C c : ℝ} (hM : 1 < M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j : ℕ) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      {q | ¬ M ^ (1 / 2 : ℝ) <
        ((syracusePassLocationRealFloorOrOne M q.1 hM.le).1 : ℝ)}).toReal ≤
      200000 * M ^ (-(1 / 12800000 : ℝ)) +
        ∑ r ∈ Finset.range j, C * (Real.log (clockScale M r)) ^ (-c) := by
  have h := clock_ladder_actual_event_le hM.le facts j 0 (Nat.zero_le j)
    {u | ¬ (clockScale M 0) ^ (1 / 2 : ℝ) < (u.1 : ℝ)}
    (reference_passage_small_landing_probability (facts 0) ((facts 0).mass_pos .alpha))
  rw [pmfProb_eq_toOuterMeasure_toReal,
    ← clock_ladder_odd_source_map_eq_actual_law hM.le j 0,
    PMF.toOuterMeasure_map_apply] at h
  simpa only [Set.preimage_setOf_eq,
    real_pass_value_congr _ hM.le (clockScale_zero M), clockScale_zero,
    Nat.Ico_zero_eq_range] using h

/-- All stage failures and the final small landing are events on the same
actual top source; the union estimate requires no independence. -/
theorem global_clock_good_failure_probability {M C c : ℝ} (hM : 1 < M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j : ℕ) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      (globalClockGoodEvent M hM.le j)ᶜ).toReal ≤ globalClockFailureBudget C c M j := by
  classical
  let μ := oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
    (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)
  let T := (realLocalClockGoodEvent (clockScale M j))ᶜ
  let S := fun i => {q : TaoOddNat |
    (syracusePassLocationRealFloorOrOne (clockScale M (i + 1)) q.1
      (one_le_clockScale hM.le (i + 1))).1 ∉
        stageClockGoodEvent (clockScale M (i + 1)) (clockScale M i)}
  let B := {q : TaoOddNat | ¬ M ^ (1 / 2 : ℝ) <
    ((syracusePassLocationRealFloorOrOne M q.1 hM.le).1 : ℝ)}
  have hsubset : (globalClockGoodEvent M hM.le j)ᶜ ⊆
      (T ∪ (⋃ i ∈ Finset.range j, S i)) ∪ B := by
    intro q hq
    by_cases ht : q ∈ T
    · exact Or.inl (Or.inl ht)
    by_cases hs : q ∈ ⋃ i ∈ Finset.range j, S i
    · exact Or.inl (Or.inr hs)
    right
    by_contra hb
    apply hq
    refine ⟨by simpa only [T, Set.mem_compl_iff, not_not] using ht, ?_, ?_⟩
    · intro i hi
      by_contra hbad
      apply hs
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hi, hbad⟩⟩
    · simpa only [B, Set.mem_setOf_eq, not_not] using hb
  have hm := pmf_outer_probability_mono_support μ (fun q hq => hsubset hq.1)
  have hu := pmf_outer_probability_union_le μ (T ∪ ⋃ i ∈ Finset.range j, S i) B
  have ht := pmf_outer_probability_union_le μ T (⋃ i ∈ Finset.range j, S i)
  have hs := pmf_outer_probability_biUnion_le μ (Finset.range j) S
  have htop := (facts j).clock_bound .alpha ((facts j).mass_pos .alpha)
  have hbottom := clock_ladder_top_source_small_landing hM facts j
  have hsum : (∑ i ∈ Finset.range j, (μ.toOuterMeasure (S i)).toReal) ≤
      ∑ i ∈ Finset.range j,
        (400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) +
          ∑ r ∈ Finset.Ico (i + 1) j, C * (Real.log (clockScale M r)) ^ (-c)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact clock_ladder_top_source_stage_bad hM facts j i (Finset.mem_range.1 hi)
  change (μ.toOuterMeasure _).toReal ≤ _
  change (μ.toOuterMeasure T).toReal ≤ _ at htop
  change (μ.toOuterMeasure B).toReal ≤ _ at hbottom
  unfold globalClockFailureBudget
  linarith

theorem global_clock_good_first_hit {M : ℝ} (hM : 1 ≤ M) (j : ℕ) (q : TaoOddNat)
    (hq : q ∈ globalClockGoodEvent M hM j) :
    ∃ τ, syracuseFirstHitAtMostReal M q.1 τ ∧
      |(τ : ℝ) - (Real.log (q.1 : ℝ) - Real.log M) / clockDrift| ≤
        20 * (Real.log (clockScale M j)) ^ (3 / 5 : ℝ) +
          ∑ i ∈ Finset.range j, 40 * (Real.log (clockScale M (i + 1))) ^ (3 / 5 : ℝ) ∧
      M ^ (1 / 2 : ℝ) < ((syracuse^[τ]) q.1 : ℝ) := by
  obtain ⟨τ, hτ, herr⟩ := real_default_landing_stage_clock (clockScale M)
    (one_le_clockScale hM) (clockScale_mono hM) q.1 j
    (20 * (Real.log (clockScale M j)) ^ (3 / 5 : ℝ))
    (fun i => 40 * (Real.log (clockScale M (i + 1))) ^ (3 / 5 : ℝ)) hq.1 hq.2.1
  simp only [clockScale_zero] at hτ herr
  refine ⟨τ, hτ, herr, ?_⟩
  simpa only [real_pass_value_eq_of_first_hit hM hτ] using hq.2.2

end CollatzClockAudit

#print axioms CollatzClockAudit.reference_passage_small_landing_probability
#print axioms CollatzClockAudit.real_pass_value_congr
#print axioms CollatzClockAudit.clock_ladder_top_source_small_landing
#print axioms CollatzClockAudit.global_clock_good_failure_probability
#print axioms CollatzClockAudit.global_clock_good_first_hit
