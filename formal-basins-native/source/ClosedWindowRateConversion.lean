import ClosedOddWeightedMeanCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.DirichletAbelian

/-- The threshold substitution x=exp(t/a) puts the two native source
windows at [exp t,exp(a t)] and [exp(a t),exp(a² t)]. -/
theorem closed_window_rate_of_logscale_rate (w : ℕ → ℝ) {a C c : ℝ}
    (ha : 0 < a)
    (h : ∀ᶠ x : ℝ in atTop,
      |closedOddWindowExpectation w (a ^ 2 * Real.log x) (a ^ 3 * Real.log x) -
        closedOddWindowExpectation w (a * Real.log x) (a ^ 2 * Real.log x)| ≤
        C * (Real.log x) ^ (-c)) :
    ∀ᶠ t : ℝ in atTop,
      |closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t)| ≤ (C * a ^ c) * t ^ (-c) := by
  have hmap : Tendsto (fun t : ℝ => Real.exp (t / a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.atTop_div_const ha tendsto_id)
  filter_upwards [hmap.eventually h, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  simp only [Real.log_exp] at ht
  have he₁ : a * (t / a) = t := by field_simp
  have he₂ : a ^ 2 * (t / a) = a * t := by field_simp
  have he₃ : a ^ 3 * (t / a) = a * (a * t) := by field_simp
  have he : (t / a) ^ (-c) = a ^ c * t ^ (-c) := by
    rw [Real.div_rpow ht0 ha.le, Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]
  simpa only [he₁, he₂, he₃, he, ← mul_assoc] using ht

theorem closed_window_discrepancy_tendsto_zero_of_rate (w : ℕ → ℝ) {a C c : ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ t : ℝ in atTop,
      |closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t)| ≤ C * t ^ (-c)) :
    Tendsto (fun t =>
      closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t)) atTop (𝓝 0) := by
  have hr : Tendsto (fun t : ℝ => C * t ^ (-c)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hc).const_mul C
  apply squeeze_zero_norm' _ hr
  simpa only [Real.norm_eq_abs] using h

/-- Eventual quantitative comparisons at two incommensurable scales
are sufficient for the actual odd harmonic mean to exist. -/
theorem odd_weighted_mean_of_two_eventual_closed_rates (w : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    {a b C c D d : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 0 < d)
    (hirr : Irrational (Real.log a / Real.log b))
    (hfirst : ∀ᶠ t : ℝ in atTop,
      |closedOddWindowExpectation w (a * t) (a * (a * t)) -
        closedOddWindowExpectation w t (a * t)| ≤ C * t ^ (-c))
    (hsecond : ∀ᶠ t : ℝ in atTop,
      |closedOddWindowExpectation w (b * t) (b * (b * t)) -
        closedOddWindowExpectation w t (b * t)| ≤ D * t ^ (-d)) :
    ∃ L : ℝ, Tendsto (fun t => oddLogarithmicCumulative w t / t) atTop (𝓝 L) := by
  have hsecond0 := closed_window_discrepancy_tendsto_zero_of_rate w hd hsecond
  obtain ⟨T, hT⟩ := eventually_atTop.mp hfirst
  let S : ℝ := max (max (max (max T 1) (Real.log 2)) (9 / (a - 1))) (9 / (b - 1))
  have hST : T ≤ S := (le_max_left _ _).trans
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hS1 : 1 ≤ S := (le_max_right _ _).trans
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hSlog : Real.log 2 ≤ S := (le_max_right _ _).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hSa : 9 / (a - 1) ≤ S := (le_max_right _ _).trans (le_max_left _ _)
  have hSb : 9 / (b - 1) ≤ S := le_max_right _ _
  have hwa : 9 ≤ (a - 1) * S := by
    have h := (div_le_iff₀ (sub_pos.mpr ha)).mp hSa
    simpa only [mul_comm] using h
  have hwb : 9 ≤ (b - 1) * S := by
    have h := (div_le_iff₀ (sub_pos.mpr hb)).mp hSb
    simpa only [mul_comm] using h
  exact odd_weighted_mean_of_closed_normalized_windows w hw0 hw1 a b S C c ha hb
    hS1 hSlog hwa hwb hC hc hc1 hirr (fun t ht => hT t (hST.trans ht)) hsecond0

#print axioms closed_window_rate_of_logscale_rate
#print axioms odd_weighted_mean_of_two_eventual_closed_rates

end CollatzCanonical.DirichletAbelian
