import SyracuseCenteredPassage
import Erdos1135.Tao.Syracuse.RealFirstPassage

open scoped BigOperators

namespace CollatzClockAudit
open Erdos1135.Tao

theorem real_first_hit_compose {x y : ℝ} {q r t : ℕ}
    (hyx : y ≤ x) (hx : syracuseFirstHitAtMostReal x q r)
    (hy : syracuseFirstHitAtMostReal y ((syracuse^[r]) q) t) :
    syracuseFirstHitAtMostReal y q (r + t) := by
  constructor
  · simpa [Nat.add_comm r t, Function.iterate_add_apply] using hy.1
  · intro k hk
    by_cases hkr : k < r
    · exact hyx.trans_lt (hx.2 k hkr)
    · have hrk : r ≤ k := by omega
      have hkt : k - r < t := by omega
      have hiter : (syracuse^[k - r]) ((syracuse^[r]) q) = (syracuse^[k]) q := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hrk]
      simpa only [hiter] using hy.2 (k - r) hkt

theorem real_first_hit_time_mono {x y : ℝ} {q r t : ℕ}
    (hyx : y ≤ x) (hx : syracuseFirstHitAtMostReal x q r)
    (hy : syracuseFirstHitAtMostReal y q t) : r ≤ t := by
  by_contra h
  have ht : t < r := by omega
  exact not_lt_of_ge (hy.1.trans hyx) (hx.2 t ht)

theorem real_first_hit_time_difference {x y : ℝ} {q r t : ℕ}
    (hyx : y ≤ x) (hx : syracuseFirstHitAtMostReal x q r)
    (hy : syracuseFirstHitAtMostReal y q t) :
    syracuseFirstHitAtMostReal y ((syracuse^[r]) q) (t - r) := by
  have hrt := real_first_hit_time_mono hyx hx hy
  constructor
  · simpa [← Function.iterate_add_apply, Nat.sub_add_cancel hrt] using hy.1
  · intro k hk
    have hkr : k + r < t := by omega
    simpa only [← Function.iterate_add_apply] using hy.2 (k + r) hkr

theorem real_first_hit_difference_clock {x y : ℝ} {q r t : ℕ} {e₁ e₂ : ℝ}
    (hyx : y ≤ x) (hx : syracuseFirstHitAtMostReal x q r)
    (hy : syracuseFirstHitAtMostReal y q t)
    (hclockx : |(r : ℝ) - (Real.log q - Real.log x) / clockDrift| ≤ e₁)
    (hclocky : |(t : ℝ) - (Real.log q - Real.log y) / clockDrift| ≤ e₂) :
    syracuseFirstHitAtMostReal y ((syracuse^[r]) q) (t - r) ∧
      |((t - r : ℕ) : ℝ) - (Real.log x - Real.log y) / clockDrift| ≤ e₁ + e₂ := by
  refine ⟨real_first_hit_time_difference hyx hx hy, ?_⟩
  have hrt := real_first_hit_time_mono hyx hx hy
  rw [Nat.cast_sub hrt]
  have hid : (t : ℝ) - r - (Real.log x - Real.log y) / clockDrift =
      ((t : ℝ) - (Real.log q - Real.log y) / clockDrift) -
        ((r : ℝ) - (Real.log q - Real.log x) / clockDrift) := by ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

def stageTime (t : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, t k

@[simp] theorem stageTime_zero (t : ℕ → ℕ) : stageTime t 0 = 0 := by
  simp [stageTime]

@[simp] theorem stageTime_succ (t : ℕ → ℕ) (n : ℕ) :
    stageTime t (n + 1) = stageTime t n + t n := by
  simp [stageTime, Finset.sum_range_succ]

/-- Every segment is a genuine successful first hit. The barriers descend,
so concatenation is the actual first hit at the final barrier. -/
theorem real_first_hit_stage_concat (b : ℕ → ℝ) (t : ℕ → ℕ) (q n : ℕ)
    (hdown : Antitone b)
    (hseg : ∀ k ≤ n,
      syracuseFirstHitAtMostReal (b k) ((syracuse^[stageTime t k]) q) (t k)) :
    syracuseFirstHitAtMostReal (b n) q (stageTime t (n + 1)) := by
  induction n with
  | zero => simpa using hseg 0 le_rfl
  | succ n ih =>
      have hfirst := ih (fun k hk => hseg k (by omega))
      have hnext := hseg (n + 1) le_rfl
      simpa only [stageTime_succ] using
        real_first_hit_compose (hdown (Nat.le_succ n)) hfirst hnext

/-- The reference values may be barrier logarithms; they need not equal
the logarithms of the actual intermediate landings. -/
theorem stage_clock_error_sum (A e : ℕ → ℝ) (t : ℕ → ℕ) (n : ℕ)
    (hclock : ∀ k < n,
      |(t k : ℝ) - (A k - A (k + 1)) / clockDrift| ≤ e k) :
    |(stageTime t n : ℝ) - (A 0 - A n) / clockDrift| ≤
      ∑ k ∈ Finset.range n, e k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev := ih (fun k hk => hclock k (by omega))
      have hnext := hclock n (by omega)
      rw [stageTime_succ, Nat.cast_add, Finset.sum_range_succ]
      have hid : (stageTime t n : ℝ) + t n - (A 0 - A (n + 1)) / clockDrift =
          ((stageTime t n : ℝ) - (A 0 - A n) / clockDrift) +
            ((t n : ℝ) - (A n - A (n + 1)) / clockDrift) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (add_le_add hprev hnext)

theorem real_first_hit_stage_clock (b A e : ℕ → ℝ) (t : ℕ → ℕ) (q n : ℕ)
    (hdown : Antitone b)
    (hseg : ∀ k ≤ n,
      syracuseFirstHitAtMostReal (b k) ((syracuse^[stageTime t k]) q) (t k))
    (hA0 : A 0 = Real.log (q : ℝ)) (hAn : A (n + 1) = Real.log (b n))
    (hclock : ∀ k ≤ n,
      |(t k : ℝ) - (A k - A (k + 1)) / clockDrift| ≤ e k) :
    syracuseFirstHitAtMostReal (b n) q (stageTime t (n + 1)) ∧
      |(stageTime t (n + 1) : ℝ) -
        (Real.log (q : ℝ) - Real.log (b n)) / clockDrift| ≤
          ∑ k ∈ Finset.range (n + 1), e k := by
  refine ⟨real_first_hit_stage_concat b t q n hdown hseg, ?_⟩
  have h := stage_clock_error_sum A e t (n + 1) (fun k hk => hclock k (by omega))
  simpa only [hA0, hAn] using h

end CollatzClockAudit
