import ClockScaleLadder
import ReferenceStageClockProbability

open scoped BigOperators

namespace CollatzClockAudit
open Erdos1135.Tao

theorem reference_stage_clock_bad_probability_of_scale_eq {C c x y : ℝ}
    (hy : 1 < y) (lower : RealClockScaleFacts C c y)
    (upper : RealClockScaleFacts C c x) (hxy : x = y ^ taoAlpha)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x .alpha) (realClockSourceHi x .alpha))) :
    pmfProb (realClockPassageLaw x upper.one_le_x .alpha hmass)
      {u | u.1 ∉ stageClockGoodEvent x y} ≤
        400000 * (Real.log y) ^ (-(1 / 10 : ℝ)) := by
  subst x
  exact reference_stage_clock_bad_probability hy lower upper hmass

theorem clock_ladder_reference_stage_bad {M C c : ℝ} (hM : 1 < M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (i : ℕ) :
    pmfProb (realClockPassageLaw (clockScale M (i + 1))
      (one_le_clockScale hM.le (i + 1)) .alpha ((facts (i + 1)).mass_pos .alpha))
      {u | u.1 ∉ stageClockGoodEvent (clockScale M (i + 1)) (clockScale M i)} ≤
        400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) := by
  exact reference_stage_clock_bad_probability_of_scale_eq (hM.trans_le (le_clockScale hM.le i))
    (facts i) (facts (i + 1)) (clockScale_succ (by linarith) i)
    ((facts (i + 1)).mass_pos .alpha)

theorem clock_ladder_actual_stage_bad {M C c : ℝ} (hM : 1 < M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j i : ℕ) (hij : i < j) :
    pmfProb (clockLadderActualLaw M hM.le j (i + 1) ((facts j).mass_pos .alpha))
      {u | u.1 ∉ stageClockGoodEvent (clockScale M (i + 1)) (clockScale M i)} ≤
        400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) +
          ∑ r ∈ Finset.Ico (i + 1) j, C * (Real.log (clockScale M r)) ^ (-c) := by
  exact clock_ladder_actual_event_le hM.le facts j (i + 1) (by omega) _
    (clock_ladder_reference_stage_bad hM facts i)

theorem clock_ladder_actual_stage_bad_geometric {M C c : ℝ} (hM : 1 < M)
    (hC : 0 ≤ C) (hc : 0 < c)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j i : ℕ) (hij : i < j) :
    pmfProb (clockLadderActualLaw M hM.le j (i + 1) ((facts j).mass_pos .alpha))
      {u | u.1 ∉ stageClockGoodEvent (clockScale M (i + 1)) (clockScale M i)} ≤
        400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) +
          C / (1 - taoAlpha ^ (-c)) * (Real.log (clockScale M (i + 1))) ^ (-c) := by
  apply (clock_ladder_actual_stage_bad hM facts j i hij).trans
  apply add_le_add le_rfl
  have hMp : 0 < M := by linarith
  simp only [clockScale_log hMp]
  exact geometric_decay_tail (Real.log_pos hM) taoAlpha_one_lt hc hC (i + 1) j

/-- Every stage event is pulled back to the single actual top source. This
is a marginal identity and introduces no independence assumption. -/
theorem clock_ladder_top_source_stage_bad {M C c : ℝ} (hM : 1 < M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i)) (j i : ℕ) (hij : i < j) :
    ((oddLogWindowOddNatPMF (realClockSourceLo (clockScale M j) .alpha)
      (realClockSourceHi (clockScale M j) .alpha) ((facts j).mass_pos .alpha)).toOuterMeasure
      {q | (syracusePassLocationRealFloorOrOne (clockScale M (i + 1)) q.1
        (one_le_clockScale hM.le (i + 1))).1 ∉
          stageClockGoodEvent (clockScale M (i + 1)) (clockScale M i)}).toReal ≤
        400000 * (Real.log (clockScale M i)) ^ (-(1 / 10 : ℝ)) +
          ∑ r ∈ Finset.Ico (i + 1) j, C * (Real.log (clockScale M r)) ^ (-c) := by
  have h := clock_ladder_actual_stage_bad hM facts j i hij
  rw [pmfProb_eq_toOuterMeasure_toReal,
    ← clock_ladder_odd_source_map_eq_actual_law hM.le j (i + 1),
    PMF.toOuterMeasure_map_apply] at h
  exact h

end CollatzClockAudit
