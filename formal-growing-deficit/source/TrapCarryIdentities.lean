import Mathlib.Data.Int.ModEq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace CollatzResearch

def trapPrefixExponent (d : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, d j

def trapScaledCarry (z q : ℤ) (p : ℕ) : ℤ := z * q * 2 ^ p

def trapCarryCoordinate (d : ℕ → ℕ) (z q : ℕ → ℤ) (i : ℕ) : ℤ :=
  trapScaledCarry (z i) (q (i + 1)) (trapPrefixExponent d i)

theorem exists_trap_carry_of_modEq {a b q : ℤ} (D : ℕ)
    (h : a ≡ 2 ^ D * b [ZMOD q]) :
    ∃ z : ℤ, a = 2 ^ D * b - z * q := by
  obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp h
  refine ⟨z, ?_⟩
  linear_combination -hz

/-- Unroll a finite recurrence with nonnegative power exponents. -/
theorem weighted_recurrence_unroll {R : Type*} [CommRing R]
    (base : R) (a c : ℕ → R) (d : ℕ → ℕ) (r : ℕ)
    (hrec : ∀ i < r, a i = base ^ d i * a (i + 1) - c i) :
    a 0 = base ^ trapPrefixExponent d r * a r -
      ∑ i ∈ Finset.range r, c i * base ^ trapPrefixExponent d i := by
  induction r with
  | zero => simp [trapPrefixExponent]
  | succ r ih =>
      have hprev := ih (fun i hi => hrec i (Nat.lt_succ_of_lt hi))
      have hlast := hrec r (Nat.lt_succ_self r)
      have hp : trapPrefixExponent d (r + 1) = trapPrefixExponent d r + d r := by
        simp [trapPrefixExponent, Finset.sum_range_succ]
      rw [hp, Finset.sum_range_succ, pow_add]
      calc
        a 0 = base ^ trapPrefixExponent d r * a r -
            ∑ i ∈ Finset.range r, c i * base ^ trapPrefixExponent d i := hprev
        _ = _ := by rw [hlast]; ring

theorem trap_carry_unroll (a q z : ℕ → ℤ) (d : ℕ → ℕ) (r : ℕ)
    (hrec : ∀ i < r, a i = 2 ^ d i * a (i + 1) - z i * q (i + 1)) :
    a 0 = 2 ^ trapPrefixExponent d r * a r -
      ∑ i ∈ Finset.range r, trapCarryCoordinate d z q i := by
  simpa only [trapCarryCoordinate, trapScaledCarry] using
    weighted_recurrence_unroll (2 : ℤ) a (fun i => z i * q (i + 1)) d r hrec

theorem trap_carry_unroll_nonzero (a q z : ℕ → ℤ) (d : ℕ → ℕ) (r : ℕ)
    (hrec : ∀ i < r, a i = 2 ^ d i * a (i + 1) - z i * q (i + 1)) :
    a 0 = 2 ^ trapPrefixExponent d r * a r -
      ∑ i ∈ (Finset.range r).filter (fun i => z i ≠ 0), trapCarryCoordinate d z q i := by
  rw [trap_carry_unroll a q z d r hrec]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : z i = 0 <;> simp [hi, trapCarryCoordinate, trapScaledCarry]

theorem trap_modulus_prefix_unroll (q : ℕ → ℤ) (m u : ℕ → ℕ) (r : ℕ)
    (hrec : ∀ i < r, q i = 9 ^ (m i + u i) * q (i + 1)) :
    q 0 = 9 ^ (trapPrefixExponent m r + trapPrefixExponent u r) * q r := by
  have h := weighted_recurrence_unroll (9 : ℤ) q (fun _ => 0)
    (fun i => m i + u i) r (by simpa using hrec)
  simpa [trapPrefixExponent, Finset.sum_add_distrib] using h

theorem trapScaledCarry_ne_zero_iff (z q : ℤ) (p : ℕ) :
    trapScaledCarry z q p ≠ 0 ↔ z ≠ 0 ∧ q ≠ 0 := by
  simp [trapScaledCarry]

theorem trapCarryCoordinate_ne_zero_iff (d : ℕ → ℕ) (z q : ℕ → ℤ) (i : ℕ) :
    trapCarryCoordinate d z q i ≠ 0 ↔ z i ≠ 0 ∧ q (i + 1) ≠ 0 :=
  trapScaledCarry_ne_zero_iff (z i) (q (i + 1)) (trapPrefixExponent d i)

theorem trapCarryCoordinate_eq_mixed_powers (d : ℕ → ℕ) (z q : ℕ → ℤ) (i s : ℕ)
    (hq : q (i + 1) = 3 ^ s) :
    trapCarryCoordinate d z q i = z i * 2 ^ trapPrefixExponent d i * 3 ^ s := by
  rw [trapCarryCoordinate, trapScaledCarry, hq]
  ring

theorem abs_trapScaledCarry_real (z q : ℤ) (p : ℕ) :
    |(trapScaledCarry z q p : ℝ)| = |(z : ℝ)| * |(q : ℝ)| * (2 : ℝ) ^ p := by
  simp [trapScaledCarry, abs_mul, abs_pow]

theorem trap_residual_div_pow_bound {b : ℤ} {epsilon q : ℝ} (h D : ℕ)
    (hb : b ≠ 0) (hbound : |(b : ℝ)| ≤ epsilon * q / (2 : ℝ) ^ h) :
    0 < |(b : ℝ)| / (2 : ℝ) ^ D ∧
      |(b : ℝ)| / (2 : ℝ) ^ D ≤ epsilon * q / (2 : ℝ) ^ (h + D) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  refine ⟨div_pos (abs_pos.mpr hbR) (by positivity), ?_⟩
  calc
    |(b : ℝ)| / (2 : ℝ) ^ D ≤ (epsilon * q / (2 : ℝ) ^ h) / (2 : ℝ) ^ D :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by rw [pow_add, div_div]

theorem trap_unrolled_residual_bound (a q z : ℕ → ℤ) (d : ℕ → ℕ) (r h : ℕ)
    (epsilon : ℝ)
    (hrec : ∀ i < r, a i = 2 ^ d i * a (i + 1) - z i * q (i + 1))
    (ha : a 0 ≠ 0) (hbound : |(a 0 : ℝ)| ≤ epsilon * (q 0 : ℝ) / (2 : ℝ) ^ h) :
    let b : ℤ := 2 ^ trapPrefixExponent d r * a r -
      ∑ i ∈ Finset.range r, trapCarryCoordinate d z q i
    0 < |(b : ℝ)| / (2 : ℝ) ^ trapPrefixExponent d r ∧
      |(b : ℝ)| / (2 : ℝ) ^ trapPrefixExponent d r ≤
        epsilon * (q 0 : ℝ) / (2 : ℝ) ^ (h + trapPrefixExponent d r) := by
  dsimp only
  rw [← trap_carry_unroll a q z d r hrec]
  exact trap_residual_div_pow_bound h (trapPrefixExponent d r) ha hbound

/-- The initial signed representative is small relative to each nonzero
carry coordinate, before introducing a mean-slope relation. -/
theorem trap_residual_to_carry_ratio_le
    {b z q0 q : ℤ} (h p M : ℕ) (epsilon : ℝ)
    (hz : z ≠ 0) (hq : 0 < q) (hmod : q0 = 9 ^ M * q)
    (hbound : |(b : ℝ)| ≤ epsilon * (q0 : ℝ) / (2 : ℝ) ^ h) :
    |(b : ℝ)| / |(trapScaledCarry z q p : ℝ)| ≤
      (epsilon / |(z : ℝ)|) * (9 : ℝ) ^ M / (2 : ℝ) ^ (h + p) := by
  have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast hz
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [abs_trapScaledCarry_real, abs_of_pos hqR]
  calc
    |(b : ℝ)| / (|(z : ℝ)| * (q : ℝ) * (2 : ℝ) ^ p) ≤
        (epsilon * (q0 : ℝ) / (2 : ℝ) ^ h) /
          (|(z : ℝ)| * (q : ℝ) * (2 : ℝ) ^ p) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by
      rw [hmod, pow_add]
      push_cast
      field_simp [hzR, hqR.ne']

/-- Ratio of an earlier carry coordinate to a later one. The natural
exponent difference is supplied as an equality, with no truncated subtraction. -/
theorem trap_carry_ratio_eq
    {zi zk qi qk : ℤ} (pi pk E M : ℕ)
    (hzk : zk ≠ 0) (hqk : 0 < qk)
    (hq : qi = 9 ^ M * qk) (hp : pk = pi + E) :
    |(trapScaledCarry zi qi pi : ℝ)| / |(trapScaledCarry zk qk pk : ℝ)| =
      (|(zi : ℝ)| / |(zk : ℝ)|) * (9 : ℝ) ^ M / (2 : ℝ) ^ E := by
  have hzkR : (zk : ℝ) ≠ 0 := by exact_mod_cast hzk
  have hqkR : (0 : ℝ) < qk := by exact_mod_cast hqk
  rw [abs_trapScaledCarry_real, abs_trapScaledCarry_real, hq, hp]
  push_cast
  rw [abs_mul, abs_pow, abs_of_pos hqkR, pow_add]
  norm_num
  field_simp [hzkR, hqkR.ne']

/-- Signed gap sums occur only through this exact integer exponent equation. -/
theorem trap_slope_factor (M U E : ℕ) (G : ℤ)
    (hE : (E : ℤ) = 4 * (M : ℤ) + G) :
    (9 : ℝ) ^ (M + U) / (2 : ℝ) ^ E =
      (9 : ℝ) ^ U * (2 : ℝ) ^ (-G) * (9 / 16 : ℝ) ^ M := by
  have hpow : (2 : ℝ) ^ E = (16 : ℝ) ^ M * (2 : ℝ) ^ G := by
    calc
      (2 : ℝ) ^ E = (2 : ℝ) ^ (E : ℤ) := by simp
      _ = (2 : ℝ) ^ (4 * (M : ℤ) + G) := by rw [hE]
      _ = (2 : ℝ) ^ (4 * (M : ℤ)) * (2 : ℝ) ^ G := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = _ := by rw [zpow_mul]; norm_num
  rw [hpow, pow_add, div_pow, zpow_neg]
  field_simp

theorem trap_residual_to_carry_ratio_le_slope
    {b z q0 q : ℤ} (h p M U : ℕ) (G : ℤ) (epsilon : ℝ)
    (hz : z ≠ 0) (hq : 0 < q) (hmod : q0 = 9 ^ (M + U) * q)
    (hexp : ((h + p : ℕ) : ℤ) = 4 * (M : ℤ) + G)
    (hbound : |(b : ℝ)| ≤ epsilon * (q0 : ℝ) / (2 : ℝ) ^ h) :
    |(b : ℝ)| / |(trapScaledCarry z q p : ℝ)| ≤
      (epsilon / |(z : ℝ)|) *
        ((9 : ℝ) ^ U * (2 : ℝ) ^ (-G) * (9 / 16 : ℝ) ^ M) := by
  have hbase := trap_residual_to_carry_ratio_le h p (M + U) epsilon hz hq hmod hbound
  rw [mul_div_assoc, trap_slope_factor M U (h + p) G hexp] at hbase
  exact hbase

theorem trap_carry_ratio_eq_slope
    {zi zk qi qk : ℤ} (pi pk E M U : ℕ) (G : ℤ)
    (hzk : zk ≠ 0) (hqk : 0 < qk)
    (hq : qi = 9 ^ (M + U) * qk) (hp : pk = pi + E)
    (hexp : (E : ℤ) = 4 * (M : ℤ) + G) :
    |(trapScaledCarry zi qi pi : ℝ)| / |(trapScaledCarry zk qk pk : ℝ)| =
      (|(zi : ℝ)| / |(zk : ℝ)|) *
        ((9 : ℝ) ^ U * (2 : ℝ) ^ (-G) * (9 / 16 : ℝ) ^ M) := by
  rw [trap_carry_ratio_eq pi pk E (M + U) hzk hqk hq hp,
    mul_div_assoc, trap_slope_factor M U E G hexp]

end CollatzResearch

#print axioms CollatzResearch.trap_carry_unroll
#print axioms CollatzResearch.trap_residual_to_carry_ratio_le_slope
#print axioms CollatzResearch.trap_carry_ratio_eq_slope
