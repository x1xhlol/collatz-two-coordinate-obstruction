import LogarithmicCumulative

set_option autoImplicit false

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

theorem finite_harmonic_lower_bound (N : ℕ) :
    Real.log ((N : ℝ) + 1) ≤ ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1 : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn1 : 0 < (N : ℝ) + 1 := by positivity
    have hn2 : 0 < (N : ℝ) + 1 + 1 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn2 hn1)
    rw [Real.log_div hn2.ne' hn1.ne'] at hlog
    have he : ((N : ℝ) + 1 + 1) / ((N : ℝ) + 1) - 1 =
        1 / ((N : ℝ) + 1) := by field_simp; ring
    rw [he] at hlog
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

theorem logarithmicCumulative_one_lower (t : ℝ) :
    t ≤ logarithmicCumulative (fun _ => 1) t := by
  have hn : Real.exp t < (⌊Real.exp t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl := Real.log_le_log (Real.exp_pos t) hn.le
  rw [Real.log_exp] at hl
  exact hl.trans (finite_harmonic_lower_bound _)

theorem logarithmicCumulative_complement (w : ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative (fun n => 1 - w n) t =
      logarithmicCumulative (fun _ => 1) t - logarithmicCumulative w t := by
  unfold logarithmicCumulative
  simp_rw [sub_div]
  rw [Finset.sum_sub_distrib]

/-- Every [0,1]-valued arithmetic weight has logarithmic cumulative increments
bounded by interval length plus one, uniformly in the starting point. -/
theorem logarithmicCumulative_increment_bound {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) :
    |logarithmicCumulative w (t + z) - logarithmicCumulative w t| ≤ z + 1 := by
  have hmon := logarithmicCumulative_monotone hw0 (by linarith : t ≤ t + z)
  rw [abs_of_nonneg (sub_nonneg.mpr hmon)]
  have hcomp := logarithmicCumulative_monotone
    (w := fun n => 1 - w n) (fun n => sub_nonneg.mpr (hw1 n))
    (by linarith : t ≤ t + z)
  rw [logarithmicCumulative_complement, logarithmicCumulative_complement] at hcomp
  have hlo := logarithmicCumulative_one_lower t
  have hhi := logarithmicCumulative_linear_bound (w := fun _ => 1)
    (fun _ => by norm_num) (fun _ => le_rfl) (by linarith : 0 ≤ t + z)
  rw [abs_of_nonneg (logarithmicCumulative_nonneg (fun _ => by norm_num) _)] at hhi
  linarith

#print axioms finite_harmonic_lower_bound
#print axioms logarithmicCumulative_increment_bound

end CollatzCanonical.DirichletAbelian
