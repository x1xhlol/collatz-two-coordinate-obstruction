import TwoScaleAveraging

set_option autoImplicit false

open Filter Topology

namespace CollatzCanonical.OddFullMean

/-- A bounded half-shift recursion transfers an odd-part logarithmic mean
to twice that mean for the full weight. The error need only be bounded. -/
theorem mean_tendsto_twice_of_half_shift (A O : ℝ → ℝ) (h B C D : ℝ)
    (hh : 0 ≤ h) (_hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hA : ∀ t : ℝ, 1 ≤ t → |A t / t| ≤ B)
    (hrec : ∀ t : ℝ, 1 ≤ t → |A (t + h) - O (t + h) - (1 / 2 : ℝ) * A t| ≤ C)
    (hO : Tendsto (fun t : ℝ => O t / t) atTop (𝓝 D)) :
    Tendsto (fun t : ℝ => A t / t) atTop (𝓝 (2 * D)) := by
  let E : ℝ → ℝ := fun t => A (max t 1) / max t 1 - 2 * D
  let Z : ℝ → ℝ := fun t => E (t + h) - (1 / 2 : ℝ) * E t
  let R : ℝ → ℝ := fun t => A (t + h) - O (t + h) - (1 / 2 : ℝ) * A t
  let W : ℝ → ℝ := fun t => (R t - (h / 2) * (A t / t)) / (t + h)
  have hshift : Tendsto (fun t : ℝ => t + h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hWbound : ∀ᶠ t : ℝ in atTop, ‖W t‖ ≤ (C + (h / 2) * B) / (t + h) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hth : 0 < t + h := by linarith
    have hhalf : 0 ≤ h / 2 := by positivity
    dsimp only [W]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hth]
    apply div_le_div_of_nonneg_right _ hth.le
    calc
      |R t - (h / 2) * (A t / t)| ≤ |R t| + |(h / 2) * (A t / t)| := abs_sub _ _
      _ = |R t| + (h / 2) * |A t / t| := by rw [abs_mul, abs_of_nonneg hhalf]
      _ ≤ C + (h / 2) * B :=
        add_le_add (hrec t ht) (mul_le_mul_of_nonneg_left (hA t ht) hhalf)
  have hWzero : Tendsto W atTop (𝓝 0) := by
    apply squeeze_zero_norm' hWbound
    exact hshift.const_div_atTop (C + (h / 2) * B)
  have hOz := (hO.comp hshift).sub_const D
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
    field_simp
    ring
  have hEbound : ∀ t : ℝ, ‖E t‖ ≤ B + |2 * D| := by
    intro t
    dsimp only [E]
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hA (max t 1) (le_max_right t 1)) le_rfl)
  have hErec : ∀ t : ℝ, E (t + h) = (1 / 2 : ℝ) • E t + Z t := by
    intro t
    simp only [Z, smul_eq_mul]
    ring
  have hElim := CollatzCanonical.TwoScale.stable_translation_tendsto_zero E Z
    (1 / 2) h (B + |2 * D|) (by norm_num) (by norm_num) hh hEbound hErec hZ
  have h := hElim.add_const (2 * D)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simp only [E, max_eq_left ht, sub_add_cancel]

end CollatzCanonical.OddFullMean
