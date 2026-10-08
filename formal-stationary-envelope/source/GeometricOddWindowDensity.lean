import GeometricCumulativeBound

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.DirichletAbelian

theorem odd_cumulative_increment_le_closed_expectation {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {s t d : ℝ}
    (hs : Real.log 2 ≤ s) (hwidth : 10 ≤ t - s) (hd : 0 ≤ d)
    (hsmall : closedOddWindowExpectation w s t ≤ d) :
    oddLogarithmicCumulative w t - oddLogarithmicCumulative w s ≤ d * (t - s) := by
  have hs0 : 0 ≤ s := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hs
  have hst : s ≤ t := by linarith
  obtain ⟨r, e, hr0, hr1, he0, _her, hnum, hmass⟩ :=
    closedOddWindow_boundary_correction hw0 hw1 hs0 hst
  have hpos : 0 < closedOddWindowMass s t := by
    rw [hmass]
    have hh := oddWindowMass_pos hs (by linarith : 8 < t - s)
    linarith
  have hupper := (abs_le.mp (odd_harmonic_window_mass_bound hs (hs.trans hst))).2
  change oddWindowMass s t - (t - s) / 2 ≤ 4 at hupper
  have hmle : closedOddWindowMass s t ≤ t - s := by rw [hmass]; linarith
  have hnumle := (div_le_iff₀ hpos).mp hsmall
  change closedOddWindowNumerator w s t ≤ d * closedOddWindowMass s t at hnumle
  rw [hnum] at hnumle
  have hh := mul_le_mul_of_nonneg_left hmle hd
  change oddWindowNumerator w s t ≤ d * (t - s)
  linarith

/-- Small normalized masses on the tail of one geometric family of closed
odd logarithmic windows give absolute logarithmic density zero. The grid base
may depend on the requested error. -/
theorem odd_logarithmic_mean_zero_of_geometric_windows {w : ℕ → ℝ} {a : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) (ha : 1 < a)
    (hsmall : ∀ d : ℝ, 0 < d → ∃ s : ℝ, 0 < s ∧
      ∀ᶠ j : ℕ in atTop,
        closedOddWindowExpectation w (a ^ j * s) (a ^ (j + 1) * s) ≤ d) :
    Tendsto (fun t : ℝ => oddLogarithmicCumulative w t / t) atTop (𝓝 0) := by
  have hweight : ∀ n, 0 ≤ if n % 2 = 1 then w n else 0 := by
    intro n
    split_ifs <;> simp [hw0]
  apply CollatzCanonical.WindowTiling.zero_mean_of_geometric_increments
    (fun t => logarithmicCumulative_nonneg hweight t)
    (logarithmicCumulative_monotone hweight) ha
  intro d hd
  obtain ⟨s, hs, hstep⟩ := hsmall d hd
  have hgrow : Tendsto (fun j : ℕ => a ^ j * s) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const hs
  have hwidth : Tendsto (fun j : ℕ => (a - 1) * (a ^ j * s)) atTop atTop :=
    hgrow.const_mul_atTop (by linarith)
  refine ⟨s, hs, ?_⟩
  filter_upwards [hstep, hgrow.eventually_ge_atTop (Real.log 2),
    hwidth.eventually_ge_atTop 10] with j hstepj hsj hwidthj
  have heq : a ^ (j + 1) * s - a ^ j * s = (a - 1) * (a ^ j * s) := by
    rw [pow_succ]
    ring
  exact odd_cumulative_increment_le_closed_expectation hw0 hw1 hsj
    (by rw [heq]; exact hwidthj) hd.le hstepj

/-- The source windows [M^(a^(j+1)), M^(a^(j+2))] used in the passage ladder
are one of the geometric families in the density criterion. -/
theorem odd_logarithmic_mean_zero_of_ladder_windows {w : ℕ → ℝ} {a : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) (ha : 1 < a)
    (hsmall : ∀ d : ℝ, 0 < d → ∃ M : ℝ, 1 < M ∧
      ∀ᶠ j : ℕ in atTop,
        closedOddWindowExpectation w (a ^ (j + 1) * Real.log M)
          (a ^ (j + 2) * Real.log M) ≤ d) :
    Tendsto (fun t : ℝ => oddLogarithmicCumulative w t / t) atTop (𝓝 0) := by
  apply odd_logarithmic_mean_zero_of_geometric_windows hw0 hw1 ha
  intro d hd
  obtain ⟨M, hM, hstep⟩ := hsmall d hd
  refine ⟨a * Real.log M, mul_pos (by linarith) (Real.log_pos hM), ?_⟩
  filter_upwards [hstep] with j hj
  simpa only [pow_succ, mul_assoc] using hj

end CollatzCanonical.DirichletAbelian
