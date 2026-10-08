import OddWindowNormalization
import IncommensurableScales
import FirstHitWordWeights

set_option autoImplicit false

open Filter Topology

namespace CollatzCanonical.DirichletAbelian

/-- A quantitative normalized-window estimate at one scale and a vanishing
estimate at an incommensurable second scale give the actual odd weighted mean.
All harmonic-mass, growth, and increment estimates are discharged here. -/
theorem odd_weighted_mean_of_normalized_windows (w : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (a b T C c : ℝ) (ha : 1 < a) (hb : 1 < b)
    (hT : 1 ≤ T) (hlog : Real.log 2 ≤ T)
    (hwidthA : 9 ≤ (a - 1) * T) (hwidthB : 9 ≤ (b - 1) * T)
    (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (hirr : Irrational (Real.log a / Real.log b))
    (hfirst : ∀ t, T ≤ t →
      |oddWindowExpectation w (a * t) (a * (a * t)) - oddWindowExpectation w t (a * t)| ≤
        C * t ^ (-c))
    (hsecond : Tendsto (fun t =>
      oddWindowExpectation w (b * t) (b * (b * t)) - oddWindowExpectation w t (b * t))
        atTop (𝓝 0)) :
    ∃ D : ℝ, Tendsto (fun t => oddLogarithmicCumulative w t / t) atTop (𝓝 D) := by
  have hT0 : 0 < T := by linarith
  have ha1 : 0 < a - 1 := sub_pos.mpr ha
  have hb1 : 0 < b - 1 := sub_pos.mpr hb
  have hodd0 (n : ℕ) : 0 ≤ if n % 2 = 1 then w n else 0 := by
    split_ifs <;> simp [hw0]
  have hodd1 (n : ℕ) : (if n % 2 = 1 then w n else 0) ≤ 1 := by
    split_ifs <;> simp [hw1]
  have hmass (d : ℝ) (hd : 1 < d) (hwidth : 9 ≤ (d - 1) * T)
      (t : ℝ) (ht : T ≤ t) :
      0 < oddWindowMass t (d * t) ∧ 0 < oddWindowMass (d * t) (d * (d * t)) := by
    have ht0 : 0 < t := hT0.trans_le ht
    have hd1 : 0 ≤ d - 1 := by linarith
    have hbase : 8 < d * t - t := by
      have hh := mul_le_mul_of_nonneg_left ht hd1
      nlinarith
    have hdt : t ≤ d * t := by nlinarith
    have hshift : 8 < d * (d * t) - d * t := by
      have hh := mul_le_mul_of_nonneg_left hdt hd1
      nlinarith
    exact ⟨oddWindowMass_pos (hlog.trans ht) hbase,
      oddWindowMass_pos ((hlog.trans ht).trans hdt) hshift⟩
  have hfirstMean (t : ℝ) (ht : T ≤ t) :
      ‖CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) a (a * t) -
        CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) a t‖ ≤
          (C / 2 + 8 / (a - 1)) * t ^ (-c) := by
    have ht1 : 1 ≤ t := hT.trans ht
    obtain ⟨hm₁, hm₂⟩ := hmass a ha hwidthA t ht
    have hh := odd_windowMean_discrepancy_bound hw0 hw1 ha (by linarith) (hlog.trans ht)
      hm₁ hm₂
    have hE := hfirst t ht
    have hi := Real.rpow_le_rpow_of_exponent_le ht1 (show (-1 : ℝ) ≤ -c by linarith)
    rw [Real.rpow_neg_one] at hi
    have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 8 / (a - 1))
    have he : 8 / ((a - 1) * t) = (8 / (a - 1)) * t⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [he] at hh
    rw [Real.norm_eq_abs]
    nlinarith
  have hsecondMean : Tendsto (fun t =>
      CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) b (b * t) -
        CollatzCanonical.TwoScale.windowMean (oddLogarithmicCumulative w) b t)
        atTop (𝓝 0) := by
    have he : Tendsto (fun t =>
        |oddWindowExpectation w (b * t) (b * (b * t)) - oddWindowExpectation w t (b * t)| / 2 +
          (8 / (b - 1)) * t⁻¹) atTop (𝓝 0) := by
      have hh := (hsecond.abs.div_const 2).add
        (tendsto_inv_atTop_zero.const_mul (8 / (b - 1)))
      simpa only [abs_zero, zero_div, mul_zero, add_zero] using hh
    apply squeeze_zero_norm' _ he
    filter_upwards [eventually_ge_atTop T] with t ht
    obtain ⟨hm₁, hm₂⟩ := hmass b hb hwidthB t ht
    have hh := odd_windowMean_discrepancy_bound hw0 hw1 hb (hT0.trans_le ht)
      (hlog.trans ht) hm₁ hm₂
    have heq : 8 / ((b - 1) * t) = (8 / (b - 1)) * t⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    simpa only [Real.norm_eq_abs, heq] using hh
  obtain ⟨D, hD, _⟩ := CollatzCanonical.TwoScale.two_scale_averaging
    (oddLogarithmicCumulative w) a b T 1 1 (C / 2 + 8 / (a - 1)) c
    ha hb hT0 (by norm_num) (by norm_num) (by positivity) hc hirr
    (fun t ht => by
      simpa only [oddLogarithmicCumulative, Real.norm_eq_abs, one_mul] using
        logarithmicCumulative_linear_bound hodd0 hodd1 (hT0.le.trans ht))
    (fun t z ht hz => by
      simpa only [oddLogarithmicCumulative, Real.norm_eq_abs, one_mul] using
        logarithmicCumulative_increment_bound hodd0 hodd1 (hT0.le.trans ht) hz)
    hfirstMean hsecondMean
  refine ⟨D, ?_⟩
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hD

/-- This criterion concerns the actual first-hit weight and the two audited
rational scales. The normalized-window estimates remain explicit inputs. -/
theorem odd_firstHitWeight_mean_of_normalized_windows (N : ℕ) (T C c : ℝ)
    (hT : 1 ≤ T) (hlog : Real.log 2 ≤ T)
    (hwidthA : 9 ≤ ((1001 / 1000 : ℝ) - 1) * T)
    (hwidthB : 9 ≤ ((2001 / 2000 : ℝ) - 1) * T)
    (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (hfirst : ∀ t, T ≤ t →
      |oddWindowExpectation (CollatzCylinderPacking.Arithmetic.firstHitWeight N)
          ((1001 / 1000 : ℝ) * t) ((1001 / 1000 : ℝ) * ((1001 / 1000 : ℝ) * t)) -
        oddWindowExpectation (CollatzCylinderPacking.Arithmetic.firstHitWeight N) t
          ((1001 / 1000 : ℝ) * t)| ≤ C * t ^ (-c))
    (hsecond : Tendsto (fun t =>
      oddWindowExpectation (CollatzCylinderPacking.Arithmetic.firstHitWeight N)
          ((2001 / 2000 : ℝ) * t) ((2001 / 2000 : ℝ) * ((2001 / 2000 : ℝ) * t)) -
        oddWindowExpectation (CollatzCylinderPacking.Arithmetic.firstHitWeight N) t
          ((2001 / 2000 : ℝ) * t)) atTop (𝓝 0)) :
    ∃ D : ℝ, Tendsto (fun t =>
      oddLogarithmicCumulative (CollatzCylinderPacking.Arithmetic.firstHitWeight N) t / t)
        atTop (𝓝 D) :=
  odd_weighted_mean_of_normalized_windows _
    (fun n => (CollatzCylinderPacking.Arithmetic.firstHitWeight_bounds N n).1)
    (fun n => (CollatzCylinderPacking.Arithmetic.firstHitWeight_bounds N n).2)
    _ _ T C c (by norm_num) (by norm_num) hT hlog hwidthA hwidthB hC hc hc1
    CollatzCanonical.Scales.logarithms_incommensurable hfirst hsecond

#print axioms odd_weighted_mean_of_normalized_windows
#print axioms odd_firstHitWeight_mean_of_normalized_windows

end CollatzCanonical.DirichletAbelian
