import GeometricOddWindowDensity

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open CollatzCanonical.DirichletAbelian CollatzCanonical.WindowTiling

/-- A fixed window allowance gives a cumulative envelope after the finite
initial part of its geometric grid. -/
theorem odd_cumulative_envelope_of_geometric_windows {w : ℕ → ℝ} {a s d : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (ha : 1 < a) (hs : 0 < s) (hd : 0 ≤ d)
    (hstep : ∀ᶠ j : ℕ in atTop,
      closedOddWindowExpectation w (a ^ j * s) (a ^ (j + 1) * s) ≤ d) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop,
      oddLogarithmicCumulative w t ≤ C + d * a * t := by
  have hweight : ∀ n, 0 ≤ if n % 2 = 1 then w n else 0 := by
    intro n
    split_ifs <;> simp [hw0]
  apply eventual_geometric_cumulative_envelope
    (logarithmicCumulative_monotone hweight) ha hs hd
  have hgrow : Tendsto (fun j : ℕ => a ^ j * s) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const hs
  have hwidth : Tendsto (fun j : ℕ => (a - 1) * (a ^ j * s)) atTop atTop :=
    hgrow.const_mul_atTop (by linarith)
  filter_upwards [hstep, hgrow.eventually_ge_atTop (Real.log 2),
    hwidth.eventually_ge_atTop 10] with j hj hsj hwj
  have heq : a ^ (j + 1) * s - a ^ j * s = (a - 1) * (a ^ j * s) := by
    rw [pow_succ]
    ring
  exact odd_cumulative_increment_le_closed_expectation hw0 hw1 hsj
    (by rw [heq]; exact hwj) hd hj

/-- The real-base passage windows start one geometric step above log m. -/
theorem odd_cumulative_envelope_of_ladder_windows {w : ℕ → ℝ} {a m d : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (ha : 1 < a) (hm : 1 < m) (hd : 0 ≤ d)
    (hstep : ∀ᶠ j : ℕ in atTop,
      closedOddWindowExpectation w (a ^ (j + 1) * Real.log m)
        (a ^ (j + 2) * Real.log m) ≤ d) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop,
      oddLogarithmicCumulative w t ≤ C + d * a * t := by
  apply odd_cumulative_envelope_of_geometric_windows hw0 hw1 ha
    (mul_pos (lt_trans zero_lt_one ha) (Real.log_pos hm)) hd
  filter_upwards [hstep] with j hj
  simpa only [pow_succ, mul_assoc] using hj

/-- The same fixed allowance in the normalized odd source mean. -/
theorem odd_normalized_cumulative_eventual_le_of_ladder_windows
    {w : ℕ → ℝ} {a m d : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (ha : 1 < a) (hm : 1 < m) (hd : 0 ≤ d)
    (hstep : ∀ᶠ j : ℕ in atTop,
      closedOddWindowExpectation w (a ^ (j + 1) * Real.log m)
        (a ^ (j + 2) * Real.log m) ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      2 * oddLogarithmicCumulative w t / t ≤ 2 * d * a + ε := by
  obtain ⟨C, hC⟩ := odd_cumulative_envelope_of_ladder_windows hw0 hw1 ha hm hd hstep
  have hlim : Tendsto (fun t : ℝ => (2 * C) / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (2 * C)
  filter_upwards [hC, hlim.eventually_lt_const hε,
    eventually_gt_atTop (0 : ℝ)] with t ht hsmall ht0
  calc
    2 * oddLogarithmicCumulative w t / t ≤ 2 * (C + d * a * t) / t :=
      div_le_div_of_nonneg_right (by linarith) ht0.le
    _ = (2 * C) / t + 2 * d * a := by field_simp
    _ ≤ 2 * d * a + ε := by linarith

#print axioms odd_cumulative_envelope_of_geometric_windows
#print axioms odd_cumulative_envelope_of_ladder_windows
#print axioms odd_normalized_cumulative_eventual_le_of_ladder_windows

end CollatzCanonical.RawOccupation
