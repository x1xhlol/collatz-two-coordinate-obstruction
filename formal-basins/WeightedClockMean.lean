import ClockCutoffBounds

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian

namespace CollatzCanonical.ClockSqueeze

noncomputable def clockTail (w : ℕ → ℝ) (d : ℕ → ℕ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑' n, if t < Real.log (n + 1 : ℕ) then clockTerm w d K n else 0

theorem clockTail_nonneg {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) (K : ℕ) (t : ℝ) : 0 ≤ clockTail w d K t := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact clockTerm_nonneg hw d K n
  · exact le_rfl

/-- A weighted logarithmic clock law and a negligible endpoint tail imply
the first-hit mean, using the actual countable depth-restricted sum. -/
theorem weighted_clock_mean {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) {lam c D : ℝ} (hlam : 0 < lam) (hc : 0 < c) (b : ℝ)
    (hs : ∀ K, Summable (clockTerm w d K))
    (hA : Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 D))
    (hbad : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative (clockBadWeight w d lam ε) t / t)
        atTop (𝓝 0))
    (htail : Tendsto (fun K : ℕ => clockTail w d K (c * (K : ℝ) + b) / (K : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => (∑' n, clockTerm w d K n) / (K : ℝ))
      atTop (𝓝 (lam * D)) := by
  let E : ℝ → ℕ → ℝ := fun ε K =>
    logarithmicCumulative (clockBadWeight w d lam ε) ((lam / (1 + ε)) * (K : ℝ)) +
    logarithmicCumulative (clockBadWeight w d lam ε) (c * (K : ℝ) + b) +
    clockTail w d K (c * (K : ℝ) + b)
  apply clock_mean_of_cumulative_bounds (E := E) hlam hA
  · intro ε hε hε1
    have hlo := scaled_cumulative_mean_tendsto (hbad ε hε hε1)
      (div_pos hlam (by linarith : 0 < 1 + ε))
    have hcut := affine_cumulative_mean_tendsto (hbad ε hε hε1) hc b
    have h := (hlo.add hcut).add htail
    simpa only [E, add_div, mul_zero, add_zero] using h
  · intro ε hε hε1
    apply Filter.Eventually.of_forall
    intro K
    have hlo := clock_lower_cumulative hw d hlam hε K (hs K)
    have hhi := clock_upper_cumulative hw d hlam hε1 K (c * (K : ℝ) + b) (hs K)
    have hb0 := logarithmicCumulative_nonneg (clockBadWeight_nonneg hw d lam ε)
      ((lam / (1 + ε)) * (K : ℝ))
    have hb1 := logarithmicCumulative_nonneg (clockBadWeight_nonneg hw d lam ε)
      (c * (K : ℝ) + b)
    have ht0 := clockTail_nonneg hw d K (c * (K : ℝ) + b)
    change (∑' n, clockTerm w d K n) ≤ _ + _ + clockTail w d K (c * (K : ℝ) + b) at hhi
    dsimp only [E]
    constructor <;> linarith

end CollatzCanonical.ClockSqueeze
