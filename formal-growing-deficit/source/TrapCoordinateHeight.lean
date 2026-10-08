import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CollatzResearch

theorem trap_coordinate_height_bound {t : ℕ} (x : Fin (t + 1) → ℤ)
    (a : ℤ) (D : ℕ) (z : Fin t → ℤ) (p s : Fin t → ℕ)
    {N B : ℝ} (hN : 0 ≤ N)
    (hhead : x 0 = 2 ^ D * a)
    (htail : ∀ i : Fin t, x i.succ = z i * 2 ^ p i * 3 ^ s i)
    (ha : |(a : ℝ)| ≤ Real.exp (Real.log 3 * N))
    (hD : (D : ℝ) ≤ B * N)
    (hz : ∀ i, |(z i : ℝ)| ≤ Real.exp N)
    (hp : ∀ i, (p i : ℝ) ≤ B * N)
    (hs : ∀ i, (s i : ℝ) ≤ N) :
    (⨆ i : Fin (t + 1), |(x i : ℝ)|) ≤
      Real.exp ((B * Real.log 2 + Real.log 3 + 1) * N) := by
  have htwo (k : ℕ) (hk : (k : ℝ) ≤ B * N) :
      (2 : ℝ) ^ k ≤ Real.exp (B * Real.log 2 * N) := by
    have h := mul_le_mul_of_nonneg_right hk (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    calc
      (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hthree (k : ℕ) (hk : (k : ℝ) ≤ N) :
      (3 : ℝ) ^ k ≤ Real.exp (Real.log 3 * N) := by
    have h := mul_le_mul_of_nonneg_right hk (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
    calc
      (3 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 3) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  apply ciSup_le
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hbound := mul_le_mul (htwo D hD) ha (abs_nonneg (a : ℝ)) (Real.exp_pos _).le
    have hx : |(x 0 : ℝ)| = (2 : ℝ) ^ D * |(a : ℝ)| := by
      rw [hhead]; push_cast; rw [abs_mul, abs_pow]; norm_num
    rw [hx]
    apply hbound.trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  · have h1 := mul_le_mul (hz j) (htwo (p j) (hp j)) (by positivity : (0 : ℝ) ≤ 2 ^ p j)
      (Real.exp_pos _).le
    have h2 := mul_le_mul h1 (hthree (s j) (hs j)) (by positivity : (0 : ℝ) ≤ 3 ^ s j)
      (by positivity : 0 ≤ Real.exp N * Real.exp (B * Real.log 2 * N))
    have hx : |(x j.succ : ℝ)| = |(z j : ℝ)| * (2 : ℝ) ^ p j * (3 : ℝ) ^ s j := by
      rw [htail]; push_cast; rw [abs_mul, abs_mul, abs_pow, abs_pow]; norm_num
    rw [hx]
    apply h2.trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

theorem abs_integer_le_exp_log_three_of_phase_bound {a : ℤ} (n h : ℕ)
    {epsilon q N : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ (3 : ℝ) ^ n) (hn : (n : ℝ) ≤ N)
    (ha : |(a : ℝ)| ≤ epsilon * q / (2 : ℝ) ^ h) :
    |(a : ℝ)| ≤ Real.exp (Real.log 3 * N) := by
  have hpow : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have htwo : (0 : ℝ) < 2 ^ h := by positivity
  have hbase : |(a : ℝ)| ≤ (3 : ℝ) ^ n := by
    calc
      |(a : ℝ)| ≤ epsilon * q / (2 : ℝ) ^ h := ha
      _ ≤ epsilon * q := div_le_self (mul_nonneg hepsilon0 hq0) hpow
      _ ≤ q := by nlinarith
      _ ≤ (3 : ℝ) ^ n := hq
  apply hbase.trans
  have hlog := mul_le_mul_of_nonneg_right hn (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  calc
    (3 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end CollatzResearch

#print axioms CollatzResearch.trap_coordinate_height_bound
#print axioms CollatzResearch.abs_integer_le_exp_log_three_of_phase_bound
