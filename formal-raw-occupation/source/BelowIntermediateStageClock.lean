import GlobalBarrierClock
import DefaultLandingStageClock

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open Erdos1135.Tao CollatzClockAudit

theorem real_pass_landing_le (x : ℝ) (hx : 1 ≤ x) (q : ℕ) :
    ((syracusePassLocationRealFloorOrOne x q hx).1 : ℝ) ≤ x := by
  have hcast : ((syracusePassLocationRealFloorOrOne x q hx).1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    exact_mod_cast (syracusePassLocationRealFloorOrOne x q hx).2
  exact hcast.trans (Nat.floor_le (zero_le_one.trans hx))

/-- Only the stages below the selected barrier contribute to this clock.
The original source can be arbitrarily far above that barrier. -/
theorem real_stage_clock_below (x : ℕ → ℝ) (hx : ∀ i, 1 ≤ x i)
    (hmono : Monotone x) (q : ℕ) (e : ℕ → ℝ) (n : ℕ)
    (hstage : ∀ i < n, ∃ t,
      syracuseFirstHitAtMostReal (x i)
        (syracusePassLocationRealFloorOrOne (x (i + 1)) q (hx (i + 1))).1 t ∧
      |(t : ℝ) - (Real.log (x (i + 1)) - Real.log (x i)) / clockDrift| ≤ e i) :
    ∃ t,
      syracuseFirstHitAtMostReal (x 0)
        (syracusePassLocationRealFloorOrOne (x n) q (hx n)).1 t ∧
      |(t : ℝ) - (Real.log (x n) - Real.log (x 0)) / clockDrift| ≤
        ∑ i ∈ Finset.range n, e i := by
  induction n with
  | zero =>
      refine ⟨0, ⟨?_, ?_⟩, ?_⟩
      · simpa using real_pass_landing_le (x 0) (hx 0) q
      · simp
      · simp
  | succ n ih =>
      obtain ⟨tlo, htlo, helo⟩ := ih (fun i hi => hstage i (by omega))
      obtain ⟨thi, hthi, hehi⟩ := hstage n (Nat.lt_succ_self n)
      have hland :
          (syracuse^[thi])
              (syracusePassLocationRealFloorOrOne (x (n + 1)) q (hx (n + 1))).1 =
            (syracusePassLocationRealFloorOrOne (x n) q (hx n)).1 := by
        rw [← real_pass_value_eq_of_first_hit (hx n) hthi]
        exact congrArg Subtype.val
          (realFloorPassOrOne_compose (hx n) (hmono (Nat.le_succ n)) (hx (n + 1)))
      have htail : syracuseFirstHitAtMostReal (x 0)
          ((syracuse^[thi])
            (syracusePassLocationRealFloorOrOne (x (n + 1)) q (hx (n + 1))).1) tlo := by
        simpa only [hland] using htlo
      refine ⟨thi + tlo,
        real_first_hit_compose (hmono (Nat.zero_le n)) hthi htail, ?_⟩
      rw [Nat.cast_add, Finset.sum_range_succ]
      have hid : (thi : ℝ) + tlo -
          (Real.log (x (n + 1)) - Real.log (x 0)) / clockDrift =
            ((thi : ℝ) - (Real.log (x (n + 1)) - Real.log (x n)) / clockDrift) +
            ((tlo : ℝ) - (Real.log (x n) - Real.log (x 0)) / clockDrift) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (by linarith)

theorem lower_clock_stage_error_sum_le {M : ℝ} (hM : 1 ≤ M) (n : ℕ) :
    (∑ i ∈ Finset.range n, 40 * (Real.log (clockScale M (i + 1))) ^ (3 / 5 : ℝ)) ≤
      globalClockErrorConstant * (Real.log (clockScale M n)) ^ (3 / 5 : ℝ) := by
  let f := fun i => (Real.log (clockScale M i)) ^ (3 / 5 : ℝ)
  have hf : ∀ i, 0 ≤ f i := fun i =>
    Real.rpow_nonneg (Real.log_nonneg (one_le_clockScale hM i)) _
  have hshift : (∑ i ∈ Finset.range n, f (i + 1)) ≤
      ∑ i ∈ Finset.range (n + 1), f i := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (hf 0)
  have hg := geometric_rpow_sum_le_last (Real.log_nonneg hM) taoAlpha_one_lt
    (by norm_num : (0 : ℝ) < 3 / 5) n
  have hMp : 0 < M := zero_lt_one.trans_le hM
  simp only [← clockScale_log hMp] at hg
  have hnonneg : 0 ≤ taoAlpha ^ (3 / 5 : ℝ) /
      (taoAlpha ^ (3 / 5 : ℝ) - 1) * f n :=
    (Finset.sum_nonneg (fun i _ => hf i)).trans hg
  rw [← Finset.mul_sum]
  change 40 * (∑ i ∈ Finset.range n, f (i + 1)) ≤
    (60 * (taoAlpha ^ (3 / 5 : ℝ) / (taoAlpha ^ (3 / 5 : ℝ) - 1))) * f n
  nlinarith

theorem global_clock_good_lower_segment {M : ℝ} (hM : 1 ≤ M)
    (j n : ℕ) (hnj : n ≤ j) (q : TaoOddNat)
    (hq : q ∈ globalClockGoodEvent M hM j) :
    ∃ t,
      syracuseFirstHitAtMostReal M
        (syracusePassLocationRealFloorOrOne (clockScale M n) q.1
          (one_le_clockScale hM n)).1 t ∧
      |(t : ℝ) - (Real.log (clockScale M n) - Real.log M) / clockDrift| ≤
        globalClockErrorConstant * (Real.log (clockScale M n)) ^ (3 / 5 : ℝ) := by
  obtain ⟨t, ht, he⟩ := real_stage_clock_below (clockScale M)
    (one_le_clockScale hM) (clockScale_mono hM) q.1
    (fun i => 40 * (Real.log (clockScale M (i + 1))) ^ (3 / 5 : ℝ)) n
    (fun i hi => hq.2.1 i (lt_of_lt_of_le hi hnj))
  refine ⟨t, ?_, ?_⟩
  · simpa only [clockScale_zero] using ht
  · simpa only [clockScale_zero] using he.trans (lower_clock_stage_error_sum_le hM n)

#print axioms real_stage_clock_below
#print axioms lower_clock_stage_error_sum_le
#print axioms global_clock_good_lower_segment

end CollatzCanonical.RawOccupation
