import GeometricOddWindowDensity

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.DirichletAbelian

/-- A uniform bound on the normalized geometric windows bounds any existing
odd logarithmic mean, with only the geometric-grid overshoot factor. -/
theorem odd_logarithmic_mean_le_of_geometric_windows {w : ℕ → ℝ} {a s d D : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (ha : 1 < a) (hs : 0 < s) (hd : 0 ≤ d)
    (hsmall : ∀ᶠ j : ℕ in atTop,
      closedOddWindowExpectation w (a ^ j * s) (a ^ (j + 1) * s) ≤ d)
    (hmean : Tendsto (fun t : ℝ => oddLogarithmicCumulative w t / t) atTop (𝓝 D)) :
    D ≤ d * a := by
  have hweight : ∀ n, 0 ≤ if n % 2 = 1 then w n else 0 := by
    intro n
    split_ifs <;> simp [hw0]
  have hgrow : Tendsto (fun j : ℕ => a ^ j * s) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const hs
  have hwidth : Tendsto (fun j : ℕ => (a - 1) * (a ^ j * s)) atTop atTop :=
    hgrow.const_mul_atTop (by linarith)
  have hstep : ∀ᶠ j : ℕ in atTop,
      oddLogarithmicCumulative w (a ^ (j + 1) * s) - oddLogarithmicCumulative w (a ^ j * s) ≤
        d * (a ^ (j + 1) * s - a ^ j * s) := by
    filter_upwards [hsmall, hgrow.eventually_ge_atTop (Real.log 2),
      hwidth.eventually_ge_atTop 10] with j hj hsj hwidthj
    have he : a ^ (j + 1) * s - a ^ j * s = (a - 1) * (a ^ j * s) := by
      rw [pow_succ]
      ring
    exact odd_cumulative_increment_le_closed_expectation hw0 hw1 hsj
      (by rw [he]; exact hwidthj) hd hj
  obtain ⟨C, hC⟩ := CollatzCanonical.WindowTiling.eventual_geometric_cumulative_envelope
    (logarithmicCumulative_monotone hweight) ha hs hd hstep
  have hlim : Tendsto (fun t : ℝ => C / t + d * a) atTop (𝓝 (d * a)) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_add] using
      (tendsto_inv_atTop_zero.const_mul C).add_const (d * a)
  apply le_of_tendsto_of_tendsto hmean hlim
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  apply (div_le_iff₀ ht0).mpr
  have hid : (C / t + d * a) * t = C + d * a * t := by field_simp
  rw [hid]
  exact ht

theorem odd_logarithmic_mean_le_of_ladder_windows {w : ℕ → ℝ} {a M d D : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (ha : 1 < a) (hM : 1 < M) (hd : 0 ≤ d)
    (hsmall : ∀ᶠ j : ℕ in atTop,
      closedOddWindowExpectation w (a ^ (j + 1) * Real.log M)
        (a ^ (j + 2) * Real.log M) ≤ d)
    (hmean : Tendsto (fun t : ℝ => oddLogarithmicCumulative w t / t) atTop (𝓝 D)) :
    D ≤ d * a := by
  apply odd_logarithmic_mean_le_of_geometric_windows hw0 hw1 ha
    (mul_pos (by linarith : 0 < a) (Real.log_pos hM)) hd _ hmean
  filter_upwards [hsmall] with j hj
  simpa only [pow_succ, mul_assoc] using hj

#print axioms odd_logarithmic_mean_le_of_ladder_windows

end CollatzCanonical.DirichletAbelian
