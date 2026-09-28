import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Topology

namespace CollatzCanonical.ClockSqueeze

/-- Bounds by convergent means at every fixed relative clock tolerance
force the unperturbed mean to converge. -/
theorem tendsto_of_clock_sandwich {f : ℕ → ℝ} {D : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ l u : ℕ → ℝ,
        Tendsto l atTop (𝓝 (D / (1 + ε))) ∧
        Tendsto u atTop (𝓝 (D / (1 - ε))) ∧
        ∀ᶠ K in atTop, l K ≤ f K ∧ f K ≤ u K) :
    Tendsto f atTop (𝓝 D) := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlo : Tendsto (fun ε : ℝ => D / (1 + ε)) (𝓝[>] 0) (𝓝 D) := by
    simpa only [add_zero, div_one] using
      (tendsto_const_nhds (x := D)).div
        ((tendsto_const_nhds (x := (1 : ℝ))).add he) (by norm_num)
  have hhi : Tendsto (fun ε : ℝ => D / (1 - ε)) (𝓝[>] 0) (𝓝 D) := by
    simpa only [sub_zero, div_one] using
      (tendsto_const_nhds (x := D)).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub he) (by norm_num)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      he.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hpos hlt
    exact ⟨hpos, hlt⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨ε, hε, hbound⟩ :=
      (hsmall.and (hlo.eventually (Ioi_mem_nhds ha))).exists
    obtain ⟨l, u, hl, _, hineq⟩ := h ε hε.1 hε.2
    filter_upwards [hineq, hl.eventually (Ioi_mem_nhds hbound)] with K hK hlK
    exact lt_of_lt_of_le hlK hK.1
  · intro b hb
    obtain ⟨ε, hε, hbound⟩ :=
      (hsmall.and (hhi.eventually (Iio_mem_nhds hb))).exists
    obtain ⟨l, u, _, hu, hineq⟩ := h ε hε.1 hε.2
    filter_upwards [hineq, hu.eventually (Iio_mem_nhds hbound)] with K hK huK
    exact lt_of_le_of_lt hK.2 huK

theorem scaled_cumulative_mean_tendsto {A : ℝ → ℝ} {D c : ℝ}
    (hA : Tendsto (fun t : ℝ => A t / t) atTop (𝓝 D)) (hc : 0 < c) :
    Tendsto (fun K : ℕ => A (c * (K : ℝ)) / (K : ℝ)) atTop (𝓝 (c * D)) := by
  have harg : Tendsto (fun K : ℕ => c * (K : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
  have h := (hA.comp harg).const_mul c
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  change c * (A (c * (K : ℝ)) / (c * (K : ℝ))) = _
  field_simp

theorem affine_cumulative_mean_tendsto {A : ℝ → ℝ} {D c : ℝ}
    (hA : Tendsto (fun t : ℝ => A t / t) atTop (𝓝 D)) (hc : 0 < c) (b : ℝ) :
    Tendsto (fun K : ℕ => A (c * (K : ℝ) + b) / (K : ℝ)) atTop (𝓝 (c * D)) := by
  have harg : Tendsto (fun K : ℕ => c * (K : ℝ) + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  have hratio : Tendsto (fun K : ℕ => (c * (K : ℝ) + b) / (K : ℝ)) atTop (𝓝 c) := by
    have h := (tendsto_const_nhds (x := c)).add (tendsto_const_div_atTop_nhds_zero_nat b)
    rw [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
    field_simp
  have h := hratio.mul (hA.comp harg)
  apply h.congr'
  filter_upwards [harg.eventually_gt_atTop (0 : ℝ)] with K hK
  have hne : c * (K : ℝ) + b ≠ 0 := ne_of_gt hK
  change ((c * (K : ℝ) + b) / (K : ℝ)) * (A (c * (K : ℝ) + b) / (c * (K : ℝ) + b)) = _
  field_simp

/-- Once the clock/cutoff comparison has been established, logarithmic
weighted density and sublinear errors yield the first-hit mean. -/
theorem clock_mean_of_cumulative_bounds {A : ℝ → ℝ} {F : ℕ → ℝ}
    {E : ℝ → ℕ → ℝ} {D lam : ℝ} (hlam : 0 < lam)
    (hA : Tendsto (fun t : ℝ => A t / t) atTop (𝓝 D))
    (hE : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun K : ℕ => E ε K / (K : ℝ)) atTop (𝓝 0))
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ K : ℕ in atTop,
      A ((lam / (1 + ε)) * (K : ℝ)) - E ε K ≤ F K ∧
      F K ≤ A ((lam / (1 - ε)) * (K : ℝ)) + E ε K) :
    Tendsto (fun K : ℕ => F K / (K : ℝ)) atTop (𝓝 (lam * D)) := by
  apply tendsto_of_clock_sandwich
  intro ε hε hε1
  refine ⟨fun K => (A ((lam / (1 + ε)) * (K : ℝ)) - E ε K) / (K : ℝ),
    fun K => (A ((lam / (1 - ε)) * (K : ℝ)) + E ε K) / (K : ℝ), ?_, ?_, ?_⟩
  · have h := (scaled_cumulative_mean_tendsto hA
      (div_pos hlam (by linarith : 0 < 1 + ε))).sub (hE ε hε hε1)
    simpa only [sub_zero, sub_div, div_mul_eq_mul_div] using h
  · have h := (scaled_cumulative_mean_tendsto hA
      (div_pos hlam (by linarith : 0 < 1 - ε))).add (hE ε hε hε1)
    simpa only [add_zero, add_div, div_mul_eq_mul_div] using h
  · filter_upwards [hbound ε hε hε1] with K hK
    exact ⟨div_le_div_of_nonneg_right hK.1 (Nat.cast_nonneg K),
      div_le_div_of_nonneg_right hK.2 (Nat.cast_nonneg K)⟩

end CollatzCanonical.ClockSqueeze
