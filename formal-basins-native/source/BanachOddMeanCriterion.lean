import ClosedOddVectorNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.BanachWindow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Actual finite odd vector sums satisfy the Banach two-scale criterion
once their inclusive normalized windows have the two stated asymptotics. -/
theorem oddVector_mean_of_eventual_closed_windows
    (F : ℕ → V) (hF : ∀ q, ‖F q‖ ≤ 1) {a b C c : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hC : 0 ≤ C) (hc : 0 < c)
    (hirr : Irrational (Real.log a / Real.log b))
    (hfirst : ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ ≤ C * t ^ (-c))
    (hsecond : Tendsto (fun t : ℝ =>
      closedOddVectorExpectation F (b * t) (b * (b * t)) -
        closedOddVectorExpectation F t (b * t)) atTop (𝓝 0)) :
    ∃ p : V, Tendsto (fun t : ℝ => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p) := by
  have ha1 : 0 < a - 1 := sub_pos.mpr ha
  let c' : ℝ := min c 1
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'1 : c' ≤ 1 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hlarge : ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ ≤ C * t ^ (-c) ∧
      1 ≤ t ∧ Real.log 2 ≤ t ∧ 9 ≤ (a - 1) * t ∧ 9 ≤ (b - 1) * t := by
    filter_upwards [hfirst, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (Real.log 2), eventually_ge_atTop (9 / (a - 1)),
      eventually_ge_atTop (9 / (b - 1))] with t ht ht1 htlog hta htb
    refine ⟨ht, ht1, htlog, ?_, ?_⟩
    · have h := (div_le_iff₀ (sub_pos.mpr ha)).mp hta
      simpa only [mul_comm] using h
    · have h := (div_le_iff₀ (sub_pos.mpr hb)).mp htb
      simpa only [mul_comm] using h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlarge
  let T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  have hTall (t : ℝ) (ht : T ≤ t) := hT₀ t ((le_max_left _ _).trans ht)
  have hfirstMean (t : ℝ) (ht : T ≤ t) :
      ‖CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a (a * t) -
        CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) a t‖ ≤
          (C / 2 + 44 / (a - 1)) * t ^ (-c') := by
    obtain ⟨hbound, ht1, hlog, hwa, _⟩ := hTall t ht
    have hraw := closedOddVector_windowMean_discrepancy hF ha hlog hwa
    have hp := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : -c ≤ -c')
    have hCp := mul_le_mul_of_nonneg_left hp hC
    have hi := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : (-1 : ℝ) ≤ -c')
    rw [Real.rpow_neg_one] at hi
    have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 44 / (a - 1))
    have he : 44 / ((a - 1) * t) = (44 / (a - 1)) * t⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [he] at hraw
    nlinarith
  have hsecondMean : Tendsto (fun t : ℝ =>
      CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) b (b * t) -
        CollatzCanonical.TwoScale.windowMean (oddVectorCumulative F) b t) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ =>
        ‖closedOddVectorExpectation F (b * t) (b * (b * t)) -
          closedOddVectorExpectation F t (b * t)‖ / 2 + (44 / (b - 1)) * t⁻¹)
        atTop (𝓝 0) := by
      have h := (hsecond.norm.div_const 2).add
        (tendsto_inv_atTop_zero.const_mul (44 / (b - 1)))
      simpa only [norm_zero, zero_div, mul_zero, add_zero] using h
    apply squeeze_zero_norm' _ he
    filter_upwards [eventually_ge_atTop T] with t ht
    obtain ⟨_, _, hlog, _, hwb⟩ := hTall t ht
    have hh := closedOddVector_windowMean_discrepancy hF hb hlog hwb
    have heq : 44 / ((b - 1) * t) = (44 / (b - 1)) * t⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    simpa only [heq] using hh
  obtain ⟨p, hp, _⟩ := CollatzCanonical.TwoScale.two_scale_averaging
    (oddVectorCumulative F) a b T 1 1 (C / 2 + 44 / (a - 1)) c'
    ha hb hT0 (by norm_num) (by norm_num) (by positivity) hc' hirr
    (fun t ht => by
      simpa only [one_mul] using oddVectorCumulative_growth hF (hT0.le.trans ht))
    (fun t z ht hz => by
      simpa only [one_mul] using oddVectorCumulative_increment hF (hT0.le.trans ht) hz)
    hfirstMean hsecondMean
  exact ⟨p, hp⟩

omit [CompleteSpace V] in
theorem closedOddVector_discrepancy_tendsto_zero_of_rate
    (F : ℕ → V) {a C c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ ≤ C * t ^ (-c)) :
    Tendsto (fun t : ℝ =>
      closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)) atTop (𝓝 0) := by
  have hr : Tendsto (fun t : ℝ => C * t ^ (-c)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hc).const_mul C
  exact squeeze_zero_norm' h hr

theorem oddVector_mean_of_two_eventual_closed_rates
    (F : ℕ → V) (hF : ∀ q, ‖F q‖ ≤ 1) {a b C c D d : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hC : 0 ≤ C) (hc : 0 < c) (hd : 0 < d)
    (hirr : Irrational (Real.log a / Real.log b))
    (hfirst : ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (a * t) (a * (a * t)) -
        closedOddVectorExpectation F t (a * t)‖ ≤ C * t ^ (-c))
    (hsecond : ∀ᶠ t : ℝ in atTop,
      ‖closedOddVectorExpectation F (b * t) (b * (b * t)) -
        closedOddVectorExpectation F t (b * t)‖ ≤ D * t ^ (-d)) :
    ∃ p : V, Tendsto (fun t : ℝ => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p) :=
  oddVector_mean_of_eventual_closed_windows F hF ha hb hC hc hirr hfirst
    (closedOddVector_discrepancy_tendsto_zero_of_rate F hd hsecond)

end CollatzCanonical.BanachWindow

#print axioms CollatzCanonical.BanachWindow.oddVector_mean_of_eventual_closed_windows
#print axioms CollatzCanonical.BanachWindow.closedOddVector_discrepancy_tendsto_zero_of_rate
#print axioms CollatzCanonical.BanachWindow.oddVector_mean_of_two_eventual_closed_rates
