import LogarithmicParity
import LogarithmicFinitePerturbation

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.Halving
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze

/-- A family of bounded nonnegative harmonic sums cannot retain mass on even
starts when each halving costs a factor one half and every odd restriction
has zero logarithmic mean. The tolerance may shrink at each halving. -/
theorem logarithmic_family_mean_zero_of_halving
    (w : ℝ → ℕ → ℝ)
    (hw : ∀ ε, 0 < ε → ∀ q, 0 ≤ w ε q ∧ w ε q ≤ 1)
    (hodd : ∀ ε, 0 < ε → Tendsto
      (fun t : ℝ => logarithmicCumulative (oddRestriction (w ε)) t / t)
      atTop (𝓝 0))
    (hhalf : ∀ ε, 0 < ε → ∀ᶠ q : ℕ in atTop, w ε (2 * q) ≤ w (ε / 2) q)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => logarithmicCumulative (w ε) t / t) atTop (𝓝 0) := by
  have hrec (e : ℝ) (he : 0 < e) : ∃ Q : ℕ, ∀ t : ℝ,
      logarithmicCumulative (w e) t ≤
        logarithmicCumulative (oddRestriction (w e)) t +
          (1 / 2 : ℝ) * logarithmicCumulative (w (e / 2)) t + (Q : ℝ) / 2 := by
    obtain ⟨Q, hQ⟩ := eventually_atTop.mp (hhalf e he)
    refine ⟨Q, ?_⟩
    intro t
    have hb := logarithmicCumulative_le_of_tail_le (Q := Q)
      (fun q => (hw e he (2 * q)).2)
      (fun q => (hw (e / 2) (by positivity) q).1)
      (fun q hq => hQ q (by omega)) (t - Real.log 2)
    have hm := logarithmicCumulative_monotone
      (fun q => (hw (e / 2) (by positivity) q).1)
      (show t - Real.log 2 ≤ t by
        have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        linarith)
    rw [logarithmic_cumulative_parity]
    linarith
  have hbound : ∀ K : ℕ, ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η →
      ∀ᶠ t : ℝ in atTop,
        logarithmicCumulative (w e) t / t ≤ 2 * (1 / 2 : ℝ) ^ K + η := by
    intro K
    induction K with
    | zero =>
      intro e he η hη
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hb := logarithmicCumulative_linear_bound
        (fun q => (hw e he q).1) (fun q => (hw e he q).2) (by linarith : 0 ≤ t)
      have hu : logarithmicCumulative (w e) t ≤ t + 1 := (le_abs_self _).trans hb
      apply (div_le_iff₀ (by linarith : 0 < t)).mpr
      norm_num
      nlinarith
    | succ K ih =>
      intro e he η hη
      obtain ⟨Q, hQ⟩ := hrec e he
      have hsmall : Tendsto
          (fun t : ℝ => logarithmicCumulative (oddRestriction (w e)) t / t +
            (Q : ℝ) / (2 * t)) atTop (𝓝 0) := by
        have hc : Tendsto (fun t : ℝ => (Q : ℝ) / (2 * t)) atTop (𝓝 0) := by
          convert (tendsto_const_nhds.div_atTop
            (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))) using 1
        simpa only [add_zero] using (hodd e he).add hc
      filter_upwards [ih (e / 2) (by positivity) η hη,
        hsmall.eventually_le_const (show 0 < η / 2 by positivity),
        eventually_gt_atTop (0 : ℝ)] with t ht hsmallt htpos
      have hr := (div_le_div_of_nonneg_right (hQ t) htpos.le)
      rw [add_div, add_div, mul_div_assoc] at hr
      have heq : (Q : ℝ) / 2 / t = (Q : ℝ) / (2 * t) := by ring
      rw [heq] at hr
      rw [pow_succ]
      nlinarith
  apply Metric.tendsto_atTop.mpr
  intro η hη
  have hp : Tendsto (fun K : ℕ => 2 * (1 / 2 : ℝ) ^ K) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  obtain ⟨K, hK⟩ := (hp.eventually_lt_const (show 0 < η / 2 by positivity)).exists
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((hbound K ε hε (η / 2) (by positivity)).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hb, htpos⟩ := hT t ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (logarithmicCumulative_nonneg (fun q => (hw ε hε q).1) t) htpos.le)]
  linarith

end CollatzCanonical.Halving

#print axioms CollatzCanonical.Halving.logarithmic_family_mean_zero_of_halving
