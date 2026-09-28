import NativeLogWindowCoordinates

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzCanonical.DirichletAbelian

theorem ratio_limit_of_bounded_difference {f g : ℝ → ℝ} {C L : ℝ}
    (hbound : ∀ᶠ t : ℝ in atTop, |f t - g t| ≤ C)
    (hg : Tendsto (fun t => g t / t) atTop (𝓝 L)) :
    Tendsto (fun t => f t / t) atTop (𝓝 L) := by
  have hz : Tendsto (fun t => (f t - g t) / t) atTop (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul C
    apply squeeze_zero_norm' _ hc
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right ht ht0.le
  simpa only [sub_div, sub_add_cancel, zero_add] using hz.add hg

theorem scaled_increment_mean_limit {f : ℝ → ℝ} {a L : ℝ} (ha : 0 < a)
    (hf : Tendsto (fun t => f t / t) atTop (𝓝 L)) :
    Tendsto (fun t => (f (a * t) - f t) / t) atTop (𝓝 ((a - 1) * L)) := by
  have hscale := (hf.comp (tendsto_id.const_mul_atTop ha)).const_mul a
  have hvalue : Tendsto (fun t => f (a * t) / t) atTop (𝓝 (a * L)) := by
    apply hscale.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [Function.comp_def, id]
    field_simp
  simpa only [Pi.sub_apply, ← sub_div, show a * L - L = (a - 1) * L by ring] using hvalue.sub hf

theorem odd_harmonic_mean_limit :
    Tendsto (fun t => oddLogarithmicCumulative (fun _ => 1) t / t)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply ratio_limit_of_bounded_difference (g := fun t => t / 2) (C := 2)
  · filter_upwards [eventually_ge_atTop (Real.log 2)] with t ht
    exact oddLogarithmicCumulative_one_bound ht
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp

theorem closed_window_mean_limit {w : ℕ → ℝ} {a L : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) (ha : 1 < a)
    (hmean : Tendsto (fun t => oddLogarithmicCumulative w t / t) atTop (𝓝 L)) :
    Tendsto (fun t => closedOddWindowExpectation w t (a * t)) atTop (𝓝 (2 * L)) := by
  have ha0 : 0 < a := by linarith
  have hnum : Tendsto (fun t => closedOddWindowNumerator w t (a * t) / t)
      atTop (𝓝 ((a - 1) * L)) := by
    apply ratio_limit_of_bounded_difference (g := fun t => oddWindowNumerator w t (a * t)) (C := 1)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨r, d, _, hr1, hd0, hdr, he, _⟩ :=
        closedOddWindow_boundary_correction (t := a * t) hw0 hw1 ht (by nlinarith)
      rw [he]
      simpa only [add_sub_cancel_left, abs_of_nonneg hd0] using hdr.trans hr1
    · exact scaled_increment_mean_limit ha0 hmean
  have hmass : Tendsto (fun t => closedOddWindowMass t (a * t) / t)
      atTop (𝓝 ((a - 1) * (1 / 2))) := by
    apply ratio_limit_of_bounded_difference (g := fun t => oddWindowMass t (a * t)) (C := 1)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨r, d, hr0, hr1, _, _, _, he⟩ :=
        closedOddWindow_boundary_correction (w := fun _ => 1) (t := a * t)
          (fun _ => by norm_num) (fun _ => le_rfl) ht (by nlinarith)
      rw [he]
      simpa only [add_sub_cancel_left, abs_of_nonneg hr0] using hr1
    · exact scaled_increment_mean_limit ha0 odd_harmonic_mean_limit
  have hquot := hnum.div hmass (by nlinarith : (a - 1) * (1 / 2 : ℝ) ≠ 0)
  have htarget : (a - 1) * L / ((a - 1) * (1 / 2 : ℝ)) = 2 * L := by
    field_simp [show a - 1 ≠ 0 by linarith]
  rw [htarget] at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [closedOddWindowExpectation]
  exact div_div_div_cancel_right₀ ht.ne' _ _

#print axioms closed_window_mean_limit

end CollatzCanonical.DirichletAbelian
