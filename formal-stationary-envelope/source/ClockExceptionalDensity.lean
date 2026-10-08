import WeightedClockMean

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian

namespace CollatzCanonical.ClockSqueeze

noncomputable def clockExceptionIndicator (P : ℕ → Prop) (d : ℕ → ℕ)
    (lam ε : ℝ) (q : ℕ) : ℝ := by
  classical
  exact if P q ∧ ¬ ((1 - ε) * Real.log (q : ℝ) / lam ≤ (d q : ℝ) ∧
      (d q : ℝ) ≤ (1 + ε) * Real.log (q : ℝ) / lam) then 1 else 0

theorem clockExceptionIndicator_nonneg (P : ℕ → Prop) (d : ℕ → ℕ)
    (lam ε : ℝ) (q : ℕ) : 0 ≤ clockExceptionIndicator P d lam ε q := by
  unfold clockExceptionIndicator
  split_ifs <;> norm_num

theorem logarithmicCumulative_le_of_weight_le {w v : ℕ → ℝ}
    (h : ∀ q, w q ≤ v q) (t : ℝ) : logarithmicCumulative w t ≤ logarithmicCumulative v t := by
  unfold logarithmicCumulative
  apply Finset.sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (h _) (by positivity)

theorem clockBadWeight_le_indicator {w : ℕ → ℝ} (hw : ∀ q, w q ≤ 1)
    (P : ℕ → Prop) (hsupport : ∀ q, ¬ P q → w q = 0)
    (d : ℕ → ℕ) (lam ε : ℝ) (q : ℕ) :
    clockBadWeight w d lam ε q ≤ clockExceptionIndicator P d lam ε q := by
  classical
  by_cases hP : P q
  · unfold clockBadWeight clockExceptionIndicator
    split_ifs <;> simp_all
  · rw [clockBadWeight, hsupport q hP]
    simp only [ite_self, clockExceptionIndicator, hP, false_and, if_false, le_refl]

/-- Absolute zero logarithmic density of the clock-exception set implies
the weighted exceptional mean is zero for every bounded supported weight. -/
theorem weighted_clock_exception_mean {w : ℕ → ℝ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1) (P : ℕ → Prop)
    (hsupport : ∀ q, ¬ P q → w q = 0) (d : ℕ → ℕ) (lam ε : ℝ)
    (hE : Tendsto (fun t : ℝ => logarithmicCumulative (clockExceptionIndicator P d lam ε) t / t)
      atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => logarithmicCumulative (clockBadWeight w d lam ε) t / t)
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hE
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact div_nonneg
      (logarithmicCumulative_nonneg (clockBadWeight_nonneg (fun q => (hw q).1) d lam ε) t) ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact div_le_div_of_nonneg_right
      (logarithmicCumulative_le_of_weight_le
        (clockBadWeight_le_indicator (fun q => (hw q).2) P hsupport d lam ε) t) ht

theorem weighted_clock_mean_of_exception_density {w : ℕ → ℝ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1) (P : ℕ → Prop)
    (hsupport : ∀ q, ¬ P q → w q = 0) (d : ℕ → ℕ)
    {lam c D : ℝ} (hlam : 0 < lam) (hc : 0 < c) (b : ℝ)
    (hs : ∀ K, Summable (clockTerm w d K))
    (hA : Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 D))
    (hE : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative (clockExceptionIndicator P d lam ε) t / t)
        atTop (𝓝 0))
    (htail : Tendsto (fun K : ℕ => clockTail w d K (c * (K : ℝ) + b) / (K : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => (∑' n, clockTerm w d K n) / (K : ℝ))
      atTop (𝓝 (lam * D)) :=
  weighted_clock_mean (fun q => (hw q).1) d hlam hc b hs hA
    (fun ε hε hε1 => weighted_clock_exception_mean hw P hsupport d lam ε (hE ε hε hε1)) htail

end CollatzCanonical.ClockSqueeze
