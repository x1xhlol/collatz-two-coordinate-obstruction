import ActualInvariantVectorMean
import ClosedWindowMeanLimit

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem vector_ratio_limit_of_bounded_difference {f g : ℝ → V} {C : ℝ} {p : V}
    (hbound : ∀ᶠ t : ℝ in atTop, ‖f t - g t‖ ≤ C)
    (hg : Tendsto (fun t => t⁻¹ • g t) atTop (𝓝 p)) :
    Tendsto (fun t => t⁻¹ • f t) atTop (𝓝 p) := by
  have hz : Tendsto (fun t => t⁻¹ • (f t - g t)) atTop (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hc
    filter_upwards [hbound, eventually_gt_atTop (0:ℝ)] with t ht ht0
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr ht0.le)
  simpa only [smul_sub, sub_add_cancel, zero_add] using hz.add hg

theorem vector_scaled_increment_mean_limit {f : ℝ → V} {a : ℝ} {p : V}
    (ha : 0 < a) (hf : Tendsto (fun t => t⁻¹ • f t) atTop (𝓝 p)) :
    Tendsto (fun t => t⁻¹ • (f (a * t) - f t)) atTop (𝓝 ((a - 1) • p)) := by
  have hscale := (hf.comp (tendsto_id.const_mul_atTop ha)).const_smul a
  have hvalue : Tendsto (fun t => t⁻¹ • f (a * t)) atTop (𝓝 (a • p)) := by
    apply hscale.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp only [Function.comp_def, id]
    rw [smul_smul]
    congr 1
    field_simp
  have htarget : a • p - p = (a - 1) • p := by rw [sub_smul, one_smul]
  simpa only [← smul_sub, htarget] using hvalue.sub hf

theorem closed_vector_window_mean_limit {F : ℕ → V} {a : ℝ} {p : V}
    (hF : ∀ q, ‖F q‖ ≤ 1) (ha : 1 < a)
    (hmean : Tendsto (fun t => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p)) :
    Tendsto (fun t => closedOddVectorExpectation F t (a * t)) atTop (𝓝 ((2:ℝ) • p)) := by
  have ha0 : 0 < a := by linarith
  have hnum : Tendsto (fun t => t⁻¹ • closedOddVectorNumerator F t (a * t))
      atTop (𝓝 ((a - 1) • p)) := by
    apply vector_ratio_limit_of_bounded_difference
      (g := fun t => oddVectorWindowNumerator F t (a * t)) (C := 1)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      obtain ⟨r, d, _, hr1, hd, he, _⟩ :=
        closedOddVector_boundary_correction hF ht (by nlinarith : t ≤ a * t)
      rw [he]
      simpa only [add_sub_cancel_left] using hd.trans hr1
    · exact vector_scaled_increment_mean_limit ha0 hmean
  have hmass : Tendsto (fun t => closedOddWindowMass t (a * t) / t)
      atTop (𝓝 ((a - 1) * (1 / 2))) := by
    apply ratio_limit_of_bounded_difference (g := fun t => oddWindowMass t (a * t)) (C := 1)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      obtain ⟨r, d, hr0, hr1, _, _, _, he⟩ :=
        closedOddWindow_boundary_correction (w := fun _ => 1) (t := a * t)
          (fun _ => by norm_num) (fun _ => le_rfl) ht (by nlinarith)
      rw [he]
      simpa only [add_sub_cancel_left, abs_of_nonneg hr0] using hr1
    · exact scaled_increment_mean_limit ha0 odd_harmonic_mean_limit
  have hquot := (hmass.inv₀ (by nlinarith : (a - 1) * (1 / 2:ℝ) ≠ 0)).smul hnum
  have htarget : ((a - 1) * (1 / 2:ℝ))⁻¹ • ((a - 1) • p) = (2:ℝ) • p := by
    rw [smul_smul]
    congr 1
    field_simp [show a - 1 ≠ 0 by linarith]
  rw [htarget] at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  unfold closedOddVectorExpectation
  rw [smul_smul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.vector_ratio_limit_of_bounded_difference
#print axioms CollatzCanonical.LabelLaw.vector_scaled_increment_mean_limit
#print axioms CollatzCanonical.LabelLaw.closed_vector_window_mean_limit
