import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CollatzResearch

/-- An exponential saving dominates a negative power of an exponentially
bounded positive size. The explicit exponent is `eta / (2 * K)`. -/
theorem eventually_product_le_neg_rpow_of_exp_bounds
    (A B M N : ℕ → ℝ) {eta K : ℝ} (heta : 0 < eta) (hK : 0 < K)
    (hB0 : ∀ᶠ n in atTop, 0 ≤ B n)
    (hM0 : ∀ᶠ n in atTop, 0 < M n)
    (hA : ∀ᶠ n in atTop, A n ≤ Real.exp (eta * N n / 2))
    (hB : ∀ᶠ n in atTop, B n ≤ Real.exp (-eta * N n))
    (hM : ∀ᶠ n in atTop, M n ≤ Real.exp (K * N n)) :
    0 < eta / (2 * K) ∧
      ∀ᶠ n in atTop, A n * B n ≤ (M n) ^ (-(eta / (2 * K))) := by
  have heps : 0 < eta / (2 * K) := by positivity
  refine ⟨heps, ?_⟩
  filter_upwards [hB0, hM0, hA, hB, hM] with n hBn hMn hAn hBn' hMn'
  have hlog : Real.log (M n) ≤ K * N n := by
    have h := Real.log_le_log hMn hMn'
    simpa only [Real.log_exp] using h
  have hsave : A n * B n ≤ Real.exp (-eta * N n / 2) := by
    calc
      A n * B n ≤ Real.exp (eta * N n / 2) * Real.exp (-eta * N n) :=
        mul_le_mul hAn hBn' hBn (Real.exp_pos _).le
      _ = Real.exp (-eta * N n / 2) := by rw [← Real.exp_add]; congr 1; ring
  apply hsave.trans
  rw [Real.rpow_def_of_pos hMn]
  apply Real.exp_le_exp.mpr
  have hscaled := mul_le_mul_of_nonneg_right hlog heps.le
  have hcancel : K * N n * (eta / (2 * K)) = eta * N n / 2 := by
    field_simp [hK.ne']
  rw [hcancel] at hscaled
  nlinarith

/-- A real sequence with an eventual exponential absolute-value bound tends
to zero whenever the ambient scale tends to positive infinity. -/
theorem tendsto_zero_of_eventually_abs_le_exp_neg
    (f N : ℕ → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hN : Tendsto N atTop atTop)
    (hf : ∀ᶠ n in atTop, |f n| ≤ Real.exp (-delta * N n)) :
    Tendsto f atTop (𝓝 0) := by
  have hscaled : Tendsto (fun n => delta * N n) atTop atTop :=
    hN.const_mul_atTop hdelta
  have hexp : Tendsto (fun n => Real.exp (-delta * N n)) atTop (𝓝 0) := by
    apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled).congr'
    filter_upwards [] with n
    change Real.exp (-(delta * N n)) = Real.exp (-delta * N n)
    congr 1
    ring
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg (f n)) hf hexp

/-- A fixed finite product of subexponential carry coefficients absorbs into
half of any prescribed positive exponential saving. This includes `t = 0`. -/
theorem eventually_prod_abs_le_exp_half_of_subexponential
    {t : ℕ} (z : ℕ → Fin t → ℝ) (N : ℕ → ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (hz : ∀ i : Fin t, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n in atTop, |z n i| ≤ Real.exp (delta * N n))
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ n in atTop, (∏ i : Fin t, |z n i|) ≤ Real.exp (eta * N n / 2) := by
  let d : ℝ := (max t 1 : ℕ)
  let delta : ℝ := eta / (2 * d)
  have hd1 : (1 : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast (le_max_right t 1)
  have hd : 0 < d := by linarith
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have ht : (t : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast (le_max_left t 1)
  have hcancel : d * delta = eta / 2 := by
    dsimp [delta]
    field_simp [hd.ne']
  have htdelta : (t : ℝ) * delta ≤ eta / 2 := by
    calc
      (t : ℝ) * delta ≤ d * delta := mul_le_mul_of_nonneg_right ht hdelta.le
      _ = eta / 2 := hcancel
  have hall : ∀ᶠ n in atTop, ∀ i : Fin t,
      |z n i| ≤ Real.exp (delta * N n) :=
    eventually_all.mpr (fun i => hz i delta hdelta)
  filter_upwards [hN, hall] with n hNn hn
  calc
    (∏ i : Fin t, |z n i|) ≤ ∏ _i : Fin t, Real.exp (delta * N n) :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hn i)
    _ = Real.exp ((t : ℝ) * (delta * N n)) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
    _ ≤ Real.exp (eta * N n / 2) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right htdelta hNn
      nlinarith

end CollatzResearch

#print axioms CollatzResearch.eventually_product_le_neg_rpow_of_exp_bounds
#print axioms CollatzResearch.tendsto_zero_of_eventually_abs_le_exp_neg
#print axioms CollatzResearch.eventually_prod_abs_le_exp_half_of_subexponential
