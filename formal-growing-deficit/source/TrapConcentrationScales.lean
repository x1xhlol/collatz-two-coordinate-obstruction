import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Sublinear concentration thresholds with vanishing polynomially weighted tails. -/

set_option autoImplicit false
open Filter
open scoped Topology

namespace Erdos1135.Tao

theorem trap_nat_rpow_sublinear (p : ℝ) (hp : p < 1) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ p ≤ gamma * (n : ℝ) := by
  intro gamma hgamma
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (p - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds hgamma), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hidentity : (n : ℝ) ^ p / (n : ℝ) = (n : ℝ) ^ (p - 1) := by
    rw [Real.rpow_sub hn0, Real.rpow_one]
  exact (div_le_iff₀ hn0).mp (hidentity.trans_le hn.le)

theorem trap_nat_ceil_rpow_sublinear (p : ℝ) (hp : p < 1) :
    ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ) ^ p⌉₊ : ℝ) ≤ gamma * (n : ℝ) := by
  intro gamma hgamma
  have hhalf : 0 < gamma / 2 := by positivity
  filter_upwards [trap_nat_rpow_sublinear p hp (gamma / 2) hhalf,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 / gamma))]
    with n hpower hn
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) p)
  have hsize := (div_le_iff₀ hgamma).mp hn
  linarith

theorem trap_tendsto_nat_mul_exp_rpow (p c : ℝ) (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-c * (n : ℝ) ^ p)) atTop (𝓝 0) := by
  have hpower := (tendsto_rpow_atTop hp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / p) c hc).comp hpower
  refine h.congr fun n => ?_
  change ((n : ℝ) ^ p) ^ (1 / p) * Real.exp (-c * (n : ℝ) ^ p) = _
  rw [← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem trap_tendsto_exp_rpow (p c : ℝ) (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ p)) atTop (𝓝 0) := by
  have hpower := (tendsto_rpow_atTop hp).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.rpow_zero, one_mul, Function.comp_def] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp hpower

theorem trap_tendsto_nat_add_one_mul_exp_rpow (p c : ℝ) (hp : 0 < p) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-c * (n : ℝ) ^ p))
      atTop (𝓝 0) := by
  simpa only [add_mul, one_mul, add_zero] using
    (trap_tendsto_nat_mul_exp_rpow p c hp hc).add (trap_tendsto_exp_rpow p c hp hc)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_nat_rpow_sublinear
#print axioms Erdos1135.Tao.trap_nat_ceil_rpow_sublinear
#print axioms Erdos1135.Tao.trap_tendsto_nat_mul_exp_rpow
#print axioms Erdos1135.Tao.trap_tendsto_exp_rpow
#print axioms Erdos1135.Tao.trap_tendsto_nat_add_one_mul_exp_rpow
