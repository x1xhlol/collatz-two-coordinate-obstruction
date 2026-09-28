import TwoScaleAveraging

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.BanachWindow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem vector_mean_tendsto_twice_of_half_shift (A O : ℝ → V) (h B C : ℝ) (p : V)
    (hh : 0 ≤ h)
    (hA : ∀ t : ℝ, 1 ≤ t → ‖t⁻¹ • A t‖ ≤ B)
    (hrec : ∀ t : ℝ, 1 ≤ t → ‖A (t + h) - O (t + h) - (1 / 2 : ℝ) • A t‖ ≤ C)
    (hO : Tendsto (fun t : ℝ => t⁻¹ • O t) atTop (𝓝 p)) :
    Tendsto (fun t : ℝ => t⁻¹ • A t) atTop (𝓝 ((2 : ℝ) • p)) := by
  let E : ℝ → V := fun t => (max t 1)⁻¹ • A (max t 1) - (2 : ℝ) • p
  let Z : ℝ → V := fun t => E (t + h) - (1 / 2 : ℝ) • E t
  let R : ℝ → V := fun t => A (t + h) - O (t + h) - (1 / 2 : ℝ) • A t
  let W : ℝ → V := fun t => (t + h)⁻¹ • (R t - (h / 2) • (t⁻¹ • A t))
  have hshift : Tendsto (fun t : ℝ => t + h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hWbound : ∀ᶠ t : ℝ in atTop, ‖W t‖ ≤ (C + (h / 2) * B) / (t + h) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hth : 0 < t + h := by linarith
    have hhalf : 0 ≤ h / 2 := by positivity
    dsimp only [W]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hth)]
    rw [show (C + (h / 2) * B) / (t + h) = (t + h)⁻¹ * (C + (h / 2) * B) by ring]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hth.le)
    calc
      ‖R t - (h / 2) • (t⁻¹ • A t)‖ ≤ ‖R t‖ + ‖(h / 2) • (t⁻¹ • A t)‖ := norm_sub_le _ _
      _ = ‖R t‖ + (h / 2) * ‖t⁻¹ • A t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hhalf]
      _ ≤ C + (h / 2) * B :=
        add_le_add (hrec t ht) (mul_le_mul_of_nonneg_left (hA t ht) hhalf)
  have hWzero : Tendsto W atTop (𝓝 0) := by
    apply squeeze_zero_norm' hWbound
    exact hshift.const_div_atTop (C + (h / 2) * B)
  have hOz := (hO.comp hshift).sub_const p
  simp only [sub_self] at hOz
  have hZ : Tendsto Z atTop (𝓝 0) := by
    have hz := hOz.add hWzero
    simp only [zero_add] at hz
    apply hz.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hth : 1 ≤ t + h := by linarith
    have ht0 : t ≠ 0 := by linarith
    have hth0 : t + h ≠ 0 := by linarith
    dsimp only [Z, E, W, R, Function.comp_def]
    rw [max_eq_left ht, max_eq_left hth]
    match_scalars <;> field_simp <;> ring
  have hEbound : ∀ t : ℝ, ‖E t‖ ≤ B + ‖(2 : ℝ) • p‖ := by
    intro t
    exact (norm_sub_le _ _).trans
      (add_le_add (hA (max t 1) (le_max_right t 1)) le_rfl)
  have hErec : ∀ t : ℝ, E (t + h) = (1 / 2 : ℝ) • E t + Z t := by
    intro t
    dsimp only [Z]
    module
  have hElim := CollatzCanonical.TwoScale.stable_translation_tendsto_zero E Z
    (1 / 2) h (B + ‖(2 : ℝ) • p‖) (by norm_num) (by norm_num) hh hEbound hErec hZ
  have h := hElim.add_const ((2 : ℝ) • p)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simp only [E, max_eq_left ht, sub_add_cancel]

end CollatzCanonical.BanachWindow

#print axioms CollatzCanonical.BanachWindow.vector_mean_tendsto_twice_of_half_shift
