import ClockExceptionalDensity

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian

namespace CollatzCanonical.ClockSqueeze

theorem logarithmicCumulative_le_of_tail_le {w v : ℕ → ℝ}
    (hw : ∀ q, w q ≤ 1) (hv : ∀ q, 0 ≤ v q) {Q : ℕ}
    (h : ∀ q, Q < q → w q ≤ v q) (t : ℝ) :
    logarithmicCumulative w t ≤ logarithmicCumulative v t + Q := by
  let S := Finset.range ⌊Real.exp t⌋₊
  have hterm (n : ℕ) : w (n + 1) / (n + 1 : ℕ) ≤
      v (n + 1) / (n + 1 : ℕ) + (if n < Q then (1 : ℝ) else 0) := by
    by_cases hn : n < Q
    · rw [if_pos hn]
      have hquot : w (n + 1) / (n + 1 : ℕ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have h1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        exact (hw _).trans h1
      have hvq := div_nonneg (hv (n + 1)) (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)
      linarith
    · rw [if_neg hn, add_zero]
      exact div_le_div_of_nonneg_right (h _ (by omega)) (by positivity)
  have hsum : (∑ n ∈ S, if n < Q then (1 : ℝ) else 0) ≤ Q := by
    rw [← Finset.sum_filter]
    calc
      (∑ n ∈ S.filter (fun n => n < Q), (1 : ℝ)) ≤ ∑ n ∈ Finset.range Q, (1 : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
        · intro n _ _
          norm_num
      _ = Q := by simp
  calc
    logarithmicCumulative w t ≤ ∑ n ∈ S,
        (v (n + 1) / (n + 1 : ℕ) + if n < Q then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = logarithmicCumulative v t + ∑ n ∈ S, if n < Q then (1 : ℝ) else 0 := by
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤ logarithmicCumulative v t + Q := add_le_add le_rfl hsum

/-- Changing finitely many values, or eventual domination, preserves zero
logarithmic mean for nonnegative weights bounded by one. -/
theorem zero_logarithmic_mean_of_eventual_le {w v : ℕ → ℝ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1) (hv : ∀ q, 0 ≤ v q)
    (h : ∀ᶠ q in atTop, w q ≤ v q)
    (hV : Tendsto (fun t : ℝ => logarithmicCumulative v t / t) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 0) := by
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp h
  have hb := logarithmicCumulative_le_of_tail_le (Q := Q) (fun q => (hw q).2) hv
    (fun q hq => hQ q (by omega))
  have hlim : Tendsto (fun t : ℝ => logarithmicCumulative v t / t + (Q : ℝ) / t)
      atTop (𝓝 0) := by
    convert hV.add (tendsto_const_nhds.div_atTop tendsto_id) using 1; simp
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact div_nonneg (logarithmicCumulative_nonneg (fun q => (hw q).1) t) ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hb t) ht.le

end CollatzCanonical.ClockSqueeze
