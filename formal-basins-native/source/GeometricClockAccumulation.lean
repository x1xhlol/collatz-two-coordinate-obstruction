import SyracuseStageClock
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped BigOperators Topology

namespace CollatzClockAudit

theorem geometric_sum_le_last {r : ℝ} (hr : 1 < r) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), r ^ i ≤ r / (r - 1) * r ^ n := by
  have hden : 0 < r - 1 := by linarith
  induction n with
  | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
      exact (le_div_iff₀ hden).2 (by linarith)
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range (n + 1), r ^ i) + r ^ (n + 1) ≤
            r / (r - 1) * r ^ n + r ^ (n + 1) := add_le_add ih le_rfl
        _ = r / (r - 1) * r ^ (n + 1) := by
          rw [pow_succ]
          field_simp
          ring

/-- Increasing geometric logarithmic scales accumulate only a constant
multiple of their largest sublinear clock error. -/
theorem geometric_rpow_sum_le_last {L a p : ℝ}
    (hL : 0 ≤ L) (ha : 1 < a) (hp : 0 < p) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (L * a ^ i) ^ p ≤
      a ^ p / (a ^ p - 1) * (L * a ^ n) ^ p := by
  have ha0 : 0 ≤ a := by linarith
  have hr : 1 < a ^ p := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt ha hp
  have hterm (i : ℕ) : (L * a ^ i) ^ p = L ^ p * (a ^ p) ^ i := by
    rw [Real.mul_rpow hL (pow_nonneg ha0 _), ← Real.rpow_pow_comm ha0]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  calc
    L ^ p * ∑ i ∈ Finset.range (n + 1), (a ^ p) ^ i ≤
        L ^ p * (a ^ p / (a ^ p - 1) * (a ^ p) ^ n) :=
      mul_le_mul_of_nonneg_left (geometric_sum_le_last hr n) (Real.rpow_nonneg hL _)
    _ = a ^ p / (a ^ p - 1) * (L ^ p * (a ^ p) ^ n) := by ring

theorem geometric_rpow_sum_le_reference {L a p Z : ℝ}
    (hL : 0 ≤ L) (ha : 1 < a) (hp : 0 < p) (n : ℕ)
    (hZ : L * a ^ n ≤ Z) :
    ∑ i ∈ Finset.range (n + 1), (L * a ^ i) ^ p ≤
      a ^ p / (a ^ p - 1) * Z ^ p := by
  have hr : 1 < a ^ p := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt ha hp
  have hc : 0 ≤ a ^ p / (a ^ p - 1) := div_nonneg (by linarith) (by linarith)
  apply (geometric_rpow_sum_le_last hL ha hp n).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg hL (pow_nonneg (by linarith) _)) hZ hp.le) hc

theorem geometric_reverse_rpow_sum_le_reference {L a p Z : ℝ}
    (hL : 0 ≤ L) (ha : 1 < a) (hp : 0 < p) (n : ℕ)
    (hZ : L * a ^ n ≤ Z) :
    ∑ i ∈ Finset.range (n + 1), (L * a ^ (n - i)) ^ p ≤
      a ^ p / (a ^ p - 1) * Z ^ p := by
  have hreflect := Finset.sum_range_reflect (fun i => (L * a ^ i) ^ p) (n + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  exact geometric_rpow_sum_le_reference hL ha hp n hZ

theorem geometric_log_scale_sum_le_source {M a p : ℝ} {q : ℕ}
    (hM : 1 ≤ M) (ha : 1 < a) (hp : 0 < p) (n : ℕ)
    (hq : M ^ (a ^ n) ≤ (q : ℝ)) :
    ∑ i ∈ Finset.range (n + 1), (Real.log (M ^ (a ^ i))) ^ p ≤
      a ^ p / (a ^ p - 1) * (Real.log (q : ℝ)) ^ p := by
  have hMp : 0 < M := by linarith
  have hlog (i : ℕ) : Real.log (M ^ (a ^ i)) = Real.log M * a ^ i := by
    rw [Real.log_rpow hMp, mul_comm]
  have htop : Real.log M * a ^ n ≤ Real.log (q : ℝ) := by
    rw [← hlog n]
    exact Real.log_le_log (Real.rpow_pos_of_pos hMp _) hq
  simp_rw [hlog]
  exact geometric_rpow_sum_le_reference (Real.log_nonneg hM) ha hp n htop

theorem clock_error_with_bounded_remainder {k τ : ℕ} {z m C R : ℝ}
    (hτk : τ ≤ k) (hrem : (k : ℝ) - τ ≤ R)
    (hclock : |(τ : ℝ) - (z - m) / clockDrift| ≤ C) :
    |(k : ℝ) - z / clockDrift| ≤ C + R + |m / clockDrift| := by
  have hτkR : (τ : ℝ) ≤ k := by exact_mod_cast hτk
  have hrest : |(k : ℝ) - τ| ≤ R := by rwa [abs_of_nonneg (sub_nonneg.mpr hτkR)]
  have hid : (k : ℝ) - z / clockDrift =
      ((τ : ℝ) - (z - m) / clockDrift) + ((k : ℝ) - τ) - m / clockDrift := by ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hclock hrest)) le_rfl)

/-- Fixed terminal remainders and a sublinear power of the source logarithm
are absorbed into any prescribed relative clock error. -/
theorem eventually_sublinear_clock_error {p C D ε : ℝ}
    (hp : p < 1) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      C * (Real.log (q : ℝ)) ^ p + D ≤ ε * Real.log (q : ℝ) / clockDrift := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun q : ℕ => C * (Real.log (q : ℝ)) ^ (-(1 - p)))
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - p)).comp hlog).const_mul C
    simpa only [Function.comp_def, mul_zero] using h
  let d := ε / (2 * clockDrift)
  have hd : 0 < d := by dsimp [d]; exact div_pos hε (by positivity [clockDrift_pos])
  filter_upwards [hratio.eventually_le_const hd, hlog.eventually_gt_atTop 0,
      hlog.eventually_ge_atTop (D / d)] with q hratioq hL hD
  have hpow : (Real.log (q : ℝ)) ^ p =
      (Real.log (q : ℝ)) ^ (-(1 - p)) * Real.log (q : ℝ) := by
    have h := Real.rpow_add hL (-(1 - p)) 1
    rw [Real.rpow_one] at h
    convert h using 1
    congr 1
    ring
  have hmain : C * (Real.log (q : ℝ)) ^ p ≤ d * Real.log (q : ℝ) := by
    rw [hpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hratioq hL.le
  have hD' : D ≤ d * Real.log (q : ℝ) := by
    have h := (div_le_iff₀ hd).mp hD
    simpa [mul_comm] using h
  have hid : d * Real.log (q : ℝ) + d * Real.log (q : ℝ) =
      ε * Real.log (q : ℝ) / clockDrift := by dsimp [d]; ring
  exact (add_le_add hmain hD').trans_eq hid

end CollatzClockAudit
