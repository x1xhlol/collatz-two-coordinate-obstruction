import ClosedOddWindowComparison

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.WindowTiling

/-- Small increments on one geometric grid control every point above its base. -/
theorem geometric_cumulative_envelope {F : ℝ → ℝ} {a s d : ℝ}
    (hF : Monotone F) (ha : 1 < a) (hs : 0 < s) (hd : 0 ≤ d)
    (hstep : ∀ n : ℕ, F (a ^ (n + 1) * s) - F (a ^ n * s) ≤
      d * (a ^ (n + 1) * s - a ^ n * s)) :
    ∀ t : ℝ, s ≤ t → F t ≤ F s + d * a * t := by
  have ha0 : 0 < a := by linarith
  have hgrid : ∀ n : ℕ, F (a ^ n * s) ≤ F s + d * (a ^ n * s - s) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have hh := hstep n; linarith
  intro t ht
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near ((one_le_div hs).mpr ht) ha
  have hnlo : a ^ n * s ≤ t := (le_div_iff₀ hs).mp hlo
  have hnhi : t < a ^ (n + 1) * s := (div_lt_iff₀ hs).mp hhi
  have hupper : a ^ (n + 1) * s ≤ a * t := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hnlo ha0.le]
  have hb := (hF hnhi.le).trans (hgrid (n + 1))
  nlinarith [mul_le_mul_of_nonneg_left hupper hd, mul_nonneg hd hs.le]

/-- A finite number of uncontrolled initial grid intervals changes only the
constant in the cumulative envelope. -/
theorem eventual_geometric_cumulative_envelope {F : ℝ → ℝ} {a s d : ℝ}
    (hF : Monotone F) (ha : 1 < a) (hs : 0 < s) (hd : 0 ≤ d)
    (hstep : ∀ᶠ n : ℕ in atTop,
      F (a ^ (n + 1) * s) - F (a ^ n * s) ≤
        d * (a ^ (n + 1) * s - a ^ n * s)) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop, F t ≤ C + d * a * t := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hstep
  let s' := a ^ J * s
  have hs' : 0 < s' := mul_pos (pow_pos (by linarith) _) hs
  have hstep' : ∀ n : ℕ, F (a ^ (n + 1) * s') - F (a ^ n * s') ≤
      d * (a ^ (n + 1) * s' - a ^ n * s') := by
    intro n
    have hh := hJ (n + J) (by omega)
    convert hh using 1 <;> simp only [s', pow_add] <;> ring_nf
  exact ⟨F s', (eventually_ge_atTop s').mono
    (fun t ht => geometric_cumulative_envelope hF ha hs' hd hstep' t ht)⟩

/-- Arbitrarily small normalized increments on possibly different geometric
grids force a nonnegative monotone cumulative function to have zero slope. -/
theorem zero_mean_of_geometric_increments {F : ℝ → ℝ} {a : ℝ}
    (hF0 : ∀ t, 0 ≤ F t) (hF : Monotone F) (ha : 1 < a)
    (hsmall : ∀ d : ℝ, 0 < d → ∃ s : ℝ, 0 < s ∧
      ∀ᶠ n : ℕ in atTop,
        F (a ^ (n + 1) * s) - F (a ^ n * s) ≤
          d * (a ^ (n + 1) * s - a ^ n * s)) :
    Tendsto (fun t : ℝ => F t / t) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ha0 : 0 < a := by linarith
  obtain ⟨s, hs, hstep⟩ := hsmall (ε / (2 * a)) (by positivity)
  obtain ⟨C, hC⟩ := eventual_geometric_cumulative_envelope hF ha hs
    (by positivity : 0 ≤ ε / (2 * a)) hstep
  have hlimit : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul C
  have hevent := hlimit.eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hC.and (hevent.and (eventually_gt_atTop (0 : ℝ))))
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hbound, hratio, ht0⟩ := hT t ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hF0 t) ht0.le)]
  have hb := (div_le_div_of_nonneg_right hbound ht0.le)
  have hid : (C + ε / (2 * a) * a * t) / t = C / t + ε / 2 := by
    field_simp
  rw [hid] at hb
  linarith

end CollatzCanonical.WindowTiling
