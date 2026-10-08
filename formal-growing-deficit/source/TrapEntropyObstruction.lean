import TrapSubspaceForms
import TrapExponentialBounds

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CollatzResearch

/-- Fixed-dimensional integer carry vectors cannot have exponentially small
residual and ordered-coordinate ratios, subexponential carry coefficients,
and an exponential entropy saving relative to an exponentially bounded height. -/
theorem false_of_trap_exponential_bounds {t : ℕ} (ht : 0 < t)
    (x : ℕ → Fin (t + 1) → ℤ)
    (a : ℕ → ℤ) (D : ℕ → ℕ) (z : ℕ → Fin t → ℤ)
    (p s : ℕ → Fin t → ℕ) (N : ℕ → ℝ)
    (hhead : ∀ n, x n 0 = 2 ^ D n * a n)
    (htail : ∀ n (i : Fin t), x n i.succ = z n i * 2 ^ p n i * 3 ^ s n i)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin t, x n i.succ ≠ 0)
    (hx : ∀ i : Fin t, ∀ᶠ n in atTop, x n i.succ ≠ 0)
    {eta K delta : ℝ} (heta : 0 < eta) (hK : 0 < K) (hdelta : 0 < delta)
    (hN : Tendsto N atTop atTop)
    (hbexp : ∀ i : Fin t, ∀ᶠ n in atTop,
      |((x n 0 - ∑ j : Fin t, x n j.succ : ℤ) : ℝ) / (x n i.succ : ℝ)| ≤
        Real.exp (-delta * N n))
    (hsepexp : ∀ i j : Fin t, i < j → ∀ᶠ n in atTop,
      |(x n i.succ : ℝ) / (x n j.succ : ℝ)| ≤ Real.exp (-delta * N n))
    (hz : ∀ i : Fin t, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |(z n i : ℝ)| ≤ Real.exp (gamma * N n))
    (hsaving : ∀ᶠ n in atTop,
      |((x n 0 - ∑ i : Fin t, x n i.succ : ℤ) : ℝ)| / (2 : ℝ) ^ D n ≤
        Real.exp (-eta * N n))
    (hheight : ∀ᶠ n in atTop,
      (⨆ i : Fin (t + 1), |(x n i : ℝ)|) ≤ Real.exp (K * N n)) :
    False := by
  have hbsmall : ∀ i : Fin t,
      Tendsto (fun n => ((x n 0 - ∑ j : Fin t, x n j.succ : ℤ) : ℝ) /
        (x n i.succ : ℝ)) atTop (𝓝 0) := by
    intro i
    exact tendsto_zero_of_eventually_abs_le_exp_neg _ N hdelta hN (hbexp i)
  have hsep : ∀ i j : Fin t, i < j →
      Tendsto (fun n => (x n i.succ : ℝ) / (x n j.succ : ℝ)) atTop (𝓝 0) := by
    intro i j hij
    exact tendsto_zero_of_eventually_abs_le_exp_neg _ N hdelta hN (hsepexp i j hij)
  have hN0 : ∀ᶠ n in atTop, 0 ≤ N n :=
    hN.eventually (eventually_ge_atTop 0)
  have hprod : ∀ᶠ n in atTop,
      (∏ i : Fin t, |(z n i : ℝ)|) ≤ Real.exp (eta * N n / 2) :=
    eventually_prod_abs_le_exp_half_of_subexponential
      (fun n i => (z n i : ℝ)) N hN0 hz heta
  let i0 : Fin t := ⟨0, ht⟩
  have hheight0 : ∀ᶠ n in atTop,
      0 < (⨆ i : Fin (t + 1), |(x n i : ℝ)|) := by
    filter_upwards [hx i0] with n hn
    have hcast : (x n i0.succ : ℝ) ≠ 0 := by exact_mod_cast hn
    exact lt_of_lt_of_le (abs_pos.mpr hcast)
      (Finite.le_ciSup (fun i : Fin (t + 1) => |(x n i : ℝ)|) i0.succ)
  have hsaving0 : ∀ᶠ n in atTop,
      0 ≤ |((x n 0 - ∑ i : Fin t, x n i.succ : ℤ) : ℝ)| / (2 : ℝ) ^ D n :=
    Eventually.of_forall fun n => by positivity
  obtain ⟨heps, hsmall⟩ := eventually_product_le_neg_rpow_of_exp_bounds
    (fun n => ∏ i : Fin t, |(z n i : ℝ)|)
    (fun n => |((x n 0 - ∑ i : Fin t, x n i.succ : ℤ) : ℝ)| / (2 : ℝ) ^ D n)
    (fun n => ⨆ i : Fin (t + 1), |(x n i : ℝ)|) N
    heta hK hsaving0 hheight0 hprod hsaving hheight
  apply not_eventually_small_carry_bound_of_trap_ratios ht heps
    x a D z p s hhead htail hb hx hbsmall hsep
  simpa only [mul_div_assoc] using hsmall

end CollatzResearch

#print axioms CollatzResearch.false_of_trap_exponential_bounds
