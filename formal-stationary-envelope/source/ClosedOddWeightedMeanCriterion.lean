import ClosedOddWindowComparison
import OddWeightedMeanCriterion

set_option autoImplicit false

open Filter Topology

namespace CollatzCanonical.DirichletAbelian

/-- The mean criterion accepts inclusive real source windows, matching Tao's
ceil/floor endpoint convention. The single lower-endpoint error is discharged. -/
theorem odd_weighted_mean_of_closed_normalized_windows (w : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (a b T C c : ℝ) (ha : 1 < a) (hb : 1 < b)
    (hT : 1 ≤ T) (hlog : Real.log 2 ≤ T)
    (hwidthA : 9 ≤ (a - 1) * T) (hwidthB : 9 ≤ (b - 1) * T)
    (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (hirr : Irrational (Real.log a / Real.log b))
    (hfirst : ∀ t, T ≤ t →
      |closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t)| ≤ C * t ^ (-c))
    (hsecond : Tendsto (fun t =>
      closedOddWindowExpectation w (b * t) (b * (b * t)) -
        closedOddWindowExpectation w t (b * t)) atTop (𝓝 0)) :
    ∃ D : ℝ, Tendsto (fun t => oddLogarithmicCumulative w t / t) atTop (𝓝 D) := by
  have ha1 : 0 < a - 1 := sub_pos.mpr ha
  have hb1 : 0 < b - 1 := sub_pos.mpr hb
  have herror (d : ℝ) (hd : 1 < d) (hwidth : 9 ≤ (d - 1) * T)
      (t : ℝ) (ht : T ≤ t) :
      |(oddWindowExpectation w (d * t) (d * (d * t)) - oddWindowExpectation w t (d * t)) -
        (closedOddWindowExpectation w (d * t) (d * (d * t)) -
          closedOddWindowExpectation w t (d * t))| ≤ (36 / (d - 1)) * t⁻¹ := by
    have hwidth' : 9 ≤ (d - 1) * t :=
      hwidth.trans (mul_le_mul_of_nonneg_left ht (by linarith))
    have hh := scaled_oddWindow_boundary_error hw0 hw1 hd (hlog.trans ht) hwidth'
    have he : 36 / ((d - 1) * t) = (36 / (d - 1)) * t⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    simpa only [he] using hh
  have hfirstOpen (t : ℝ) (ht : T ≤ t) :
      |oddWindowExpectation w (a * t) (a * (a * t)) - oddWindowExpectation w t (a * t)| ≤
        (C + 36 / (a - 1)) * t ^ (-c) := by
    have he := herror a ha hwidthA t ht
    have hclosed := hfirst t ht
    have htri := abs_sub_le
      (oddWindowExpectation w (a * t) (a * (a * t)) - oddWindowExpectation w t (a * t))
      (closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t)) 0
    simp only [sub_zero] at htri
    have hi := Real.rpow_le_rpow_of_exponent_le (hT.trans ht)
      (show (-1 : ℝ) ≤ -c by linarith)
    rw [Real.rpow_neg_one] at hi
    have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 36 / (a - 1))
    nlinarith
  have hgap : Tendsto (fun t =>
      (oddWindowExpectation w (b * t) (b * (b * t)) - oddWindowExpectation w t (b * t)) -
        (closedOddWindowExpectation w (b * t) (b * (b * t)) -
          closedOddWindowExpectation w t (b * t))) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => (36 / (b - 1)) * t⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (36 / (b - 1))
    apply squeeze_zero_norm' _ he
    filter_upwards [eventually_ge_atTop T] with t ht
    simpa only [Real.norm_eq_abs] using herror b hb hwidthB t ht
  have hsecondOpen : Tendsto (fun t =>
      oddWindowExpectation w (b * t) (b * (b * t)) - oddWindowExpectation w t (b * t))
        atTop (𝓝 0) := by
    have hh := hsecond.add hgap
    simp only [add_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun t => by ring)
  exact odd_weighted_mean_of_normalized_windows w hw0 hw1 a b T (C + 36 / (a - 1)) c
    ha hb hT hlog hwidthA hwidthB (by positivity) hc hc1 hirr hfirstOpen hsecondOpen

#print axioms odd_weighted_mean_of_closed_normalized_windows

end CollatzCanonical.DirichletAbelian
