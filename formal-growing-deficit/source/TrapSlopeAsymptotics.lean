import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzResearch

theorem trap_entropy_saving_bound (n H : ℕ) {epsilon eta N : ℝ}
    (hepsilon : epsilon ≤ 1)
    (hgap : (n : ℝ) * Real.log 3 + eta * N ≤ (H : ℝ) * Real.log 2) :
    epsilon * (3 : ℝ) ^ n / (2 : ℝ) ^ H ≤ Real.exp (-eta * N) := by
  have htwo : (0 : ℝ) < 2 ^ H := by positivity
  calc
    epsilon * (3 : ℝ) ^ n / (2 : ℝ) ^ H ≤ (3 : ℝ) ^ n / (2 : ℝ) ^ H := by
      exact div_le_div_of_nonneg_right
        (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) n]) htwo.le
    _ = Real.exp ((n : ℝ) * Real.log 3 - (H : ℝ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 3),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-eta * N) := Real.exp_le_exp.mpr (by linarith)

theorem trap_slope_factor_eq_exp (M U : ℕ) (G : ℤ) :
    (9 : ℝ) ^ U * (2 : ℝ) ^ (-G) * (9 / 16 : ℝ) ^ M =
      Real.exp ((U : ℝ) * Real.log 9 - (G : ℝ) * Real.log 2 -
        Real.log (16 / 9) * (M : ℝ)) := by
  have hlog : Real.log (9 / 16 : ℝ) = -Real.log (16 / 9) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num)]
    ring
  rw [show (U : ℝ) * Real.log 9 - (G : ℝ) * Real.log 2 -
      Real.log (16 / 9) * (M : ℝ) =
      (U : ℝ) * Real.log 9 + (-G : ℤ) * Real.log 2 +
        (M : ℝ) * Real.log (9 / 16) by rw [hlog]; push_cast; ring]
  have hz : Real.exp ((-G : ℤ) * Real.log 2) = (2 : ℝ) ^ (-G) := by
    rw [← Real.log_zpow, Real.exp_log (by positivity)]
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
    hz, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 9),
    Real.exp_log (by norm_num : (0 : ℝ) < 9 / 16)]

theorem eventually_linear_error_bound (U G N : ℕ → ℝ) (a b : ℝ)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (hU : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |U n| ≤ gamma * N n)
    (hG : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n in atTop, |G n| ≤ gamma * N n) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |a * U n + b * G n| ≤ gamma * N n := by
  intro gamma hgamma
  let d := |a| + |b| + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < gamma / d := div_pos hgamma hd
  filter_upwards [hN, hU (gamma / d) hq, hG (gamma / d) hq] with n hn hu hg
  calc
    |a * U n + b * G n| ≤ |a| * |U n| + |b| * |G n| := by
      simpa only [abs_mul] using abs_add_le (a * U n) (b * G n)
    _ ≤ |a| * (gamma / d * N n) + |b| * (gamma / d * N n) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hg (abs_nonneg _))
    _ ≤ gamma * N n := by
      have hcoef : (|a| + |b|) * (gamma / d) ≤ gamma := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hd).mpr
        dsimp [d]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef hn]

theorem eventually_exp_separation_of_sublinear_error
    (C E M N : ℕ → ℝ) {c delta : ℝ} (hc : 0 < c) (hdelta : 0 < delta)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (hM : ∀ᶠ n in atTop, delta * N n ≤ M n)
    (hC : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, C n ≤ Real.exp (gamma * N n))
    (hE : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |E n| ≤ gamma * N n) :
    ∀ᶠ n in atTop, C n * Real.exp (E n - c * M n) ≤
      Real.exp (-(c * delta / 2) * N n) := by
  have hgamma : 0 < c * delta / 4 := by positivity
  filter_upwards [hN, hM, hC (c * delta / 4) hgamma,
    hE (c * delta / 4) hgamma] with n hn hm hcn hen
  calc
    C n * Real.exp (E n - c * M n) ≤
        Real.exp ((c * delta / 4) * N n) * Real.exp (E n - c * M n) :=
      mul_le_mul_of_nonneg_right hcn (Real.exp_pos _).le
    _ = Real.exp ((c * delta / 4) * N n + E n - c * M n) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(c * delta / 2) * N n) := by
      apply Real.exp_le_exp.mpr
      have he := (le_abs_self (E n)).trans hen
      nlinarith [mul_le_mul_of_nonneg_left hm hc.le]

theorem eventually_trap_slope_separation
    (C N : ℕ → ℝ) (M U : ℕ → ℕ) (G : ℕ → ℤ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hN : ∀ᶠ n in atTop, 0 ≤ N n)
    (hM : ∀ᶠ n in atTop, delta * N n ≤ (M n : ℝ))
    (hC : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, C n ≤ Real.exp (gamma * N n))
    (hU : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, (U n : ℝ) ≤ gamma * N n)
    (hG : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |(G n : ℝ)| ≤ gamma * N n) :
    ∀ᶠ n in atTop,
      C n * ((9 : ℝ) ^ U n * (2 : ℝ) ^ (-G n) * (9 / 16 : ℝ) ^ M n) ≤
        Real.exp (-(Real.log (16 / 9) * delta / 2) * N n) := by
  have hc : 0 < Real.log (16 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hU' : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, |(U n : ℝ)| ≤ gamma * N n := by
    intro gamma hgamma
    simpa only [Nat.abs_cast] using hU gamma hgamma
  have hE := eventually_linear_error_bound (fun n => (U n : ℝ))
    (fun n => (G n : ℝ)) N (Real.log 9) (-Real.log 2) hN hU' hG
  have h := eventually_exp_separation_of_sublinear_error C
    (fun n => Real.log 9 * (U n : ℝ) + -Real.log 2 * (G n : ℝ))
    (fun n => (M n : ℝ)) N hc hdelta hN hM hC hE
  filter_upwards [h] with n hn
  rw [trap_slope_factor_eq_exp]
  have heq : (U n : ℝ) * Real.log 9 - (G n : ℝ) * Real.log 2 -
      Real.log (16 / 9) * (M n : ℝ) =
      Real.log 9 * (U n : ℝ) + -Real.log 2 * (G n : ℝ) -
        Real.log (16 / 9) * (M n : ℝ) := by ring
  rw [heq]
  exact hn

theorem trap_zero_carry_residual_ge_one {a b : ℤ} (D : ℕ)
    (hb : b ≠ 0) (heq : b = 2 ^ D * a) :
    1 ≤ |(b : ℝ)| / (2 : ℝ) ^ D := by
  have ha : a ≠ 0 := by intro h; simp [h] at heq; exact hb heq
  have habs : (1 : ℝ) ≤ |(a : ℝ)| := by
    have hz : (0 : ℤ) < |a| := abs_pos.mpr ha
    exact_mod_cast (show (1 : ℤ) ≤ |a| by omega)
  rw [heq]
  push_cast
  rw [abs_mul, abs_pow]
  norm_num
  simpa using habs

end CollatzResearch

#print axioms CollatzResearch.eventually_trap_slope_separation
#print axioms CollatzResearch.trap_entropy_saving_bound
