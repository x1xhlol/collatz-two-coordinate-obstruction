import SyracuseStageClock
import DefaultPassComposition

open scoped BigOperators

namespace CollatzClockAudit
open Erdos1135.Tao

/-- Each lower stage is tested on its own totalized landing from the fixed
original source. Induction identifies that landing with an actual iterate
only after establishing the preceding successful first hit. -/
theorem real_default_landing_stage_clock_from (x : ℕ → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hmono : Monotone x) (q j : ℕ) (etop : ℝ) (e : ℕ → ℝ)
    (htop : ∃ τ, syracuseFirstHitAtMostReal (x j) q τ ∧
      |(τ : ℝ) - (Real.log (q : ℝ) - Real.log (x j)) / clockDrift| ≤ etop)
    (hstage : ∀ i < j, ∃ t,
      syracuseFirstHitAtMostReal (x i)
        (syracusePassLocationRealFloorOrOne (x (i + 1)) q (hx (i + 1))).1 t ∧
      |(t : ℝ) - (Real.log (x (i + 1)) - Real.log (x i)) / clockDrift| ≤ e i)
    (i : ℕ) (hij : i ≤ j) :
    ∃ τ, syracuseFirstHitAtMostReal (x i) q τ ∧
      |(τ : ℝ) - (Real.log (q : ℝ) - Real.log (x i)) / clockDrift| ≤
        etop + ∑ r ∈ Finset.Ico i j, e r := by
  refine Nat.decreasingInduction (motive := fun i _ =>
    ∃ τ, syracuseFirstHitAtMostReal (x i) q τ ∧
      |(τ : ℝ) - (Real.log (q : ℝ) - Real.log (x i)) / clockDrift| ≤
        etop + ∑ r ∈ Finset.Ico i j, e r) ?_ ?_ hij
  · intro k hk ih
    obtain ⟨r, hr, hrc⟩ := ih
    obtain ⟨t, ht, htc⟩ := hstage k hk
    rw [real_pass_value_eq_of_first_hit (hx (k + 1)) hr] at ht
    refine ⟨r + t, real_first_hit_compose (hmono (Nat.le_succ k)) hr ht, ?_⟩
    have hid : ((r + t : ℕ) : ℝ) -
        (Real.log (q : ℝ) - Real.log (x k)) / clockDrift =
          ((r : ℝ) - (Real.log (q : ℝ) - Real.log (x (k + 1))) / clockDrift) +
            ((t : ℝ) - (Real.log (x (k + 1)) - Real.log (x k)) / clockDrift) := by
      push_cast
      ring
    rw [hid]
    have hbound := (abs_add_le _ _).trans (add_le_add hrc htc)
    have hsum : (etop + ∑ r ∈ Finset.Ico (k + 1) j, e r) + e k =
        etop + ∑ r ∈ Finset.Ico k j, e r := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hk]
      ring
    exact hbound.trans_eq hsum
  · simpa using htop

theorem real_default_landing_stage_clock (x : ℕ → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hmono : Monotone x) (q j : ℕ) (etop : ℝ) (e : ℕ → ℝ)
    (htop : ∃ τ, syracuseFirstHitAtMostReal (x j) q τ ∧
      |(τ : ℝ) - (Real.log (q : ℝ) - Real.log (x j)) / clockDrift| ≤ etop)
    (hstage : ∀ i < j, ∃ t,
      syracuseFirstHitAtMostReal (x i)
        (syracusePassLocationRealFloorOrOne (x (i + 1)) q (hx (i + 1))).1 t ∧
      |(t : ℝ) - (Real.log (x (i + 1)) - Real.log (x i)) / clockDrift| ≤ e i) :
    ∃ τ, syracuseFirstHitAtMostReal (x 0) q τ ∧
      |(τ : ℝ) - (Real.log (q : ℝ) - Real.log (x 0)) / clockDrift| ≤
        etop + ∑ r ∈ Finset.range j, e r := by
  simpa only [Nat.Ico_zero_eq_range] using
    real_default_landing_stage_clock_from x hx hmono q j etop e htop hstage 0 (Nat.zero_le j)

end CollatzClockAudit
