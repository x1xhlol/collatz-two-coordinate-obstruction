import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CollatzResearch.PositivePrefixArithmetic

theorem dyadic_window (p N : ℕ) (hp : 0 < p) (hpN : p < N) :
    ∃ L : ℕ, N ≤ p * 2 ^ L ∧ p * 2 ^ L < 2 * N := by
  have hex : ∃ L : ℕ, N ≤ p * 2 ^ L := by
    refine ⟨N, ?_⟩
    have hn := (Nat.lt_two_pow_self (n := N)).le
    have hm : 2 ^ N ≤ p * 2 ^ N := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ N) (show 1 ≤ p by omega)
    exact hn.trans hm
  have hL := Nat.find_spec hex
  have hnz : Nat.find hex ≠ 0 := by
    intro hz
    simp only [hz, pow_zero, mul_one] at hL
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnz
  have hprev : p * 2 ^ k < N := Nat.lt_of_not_ge
    (Nat.find_min hex (show k < Nat.find hex by omega))
  refine ⟨Nat.find hex, hL, ?_⟩
  rw [hk, pow_succ]
  nlinarith only [hprev]

theorem prefix_power_window (p n : ℕ) (hp : 4 ≤ p) (hp7 : p ≤ 7) :
    ∃ L : ℕ, 3 ^ (2 * (n + 1)) ≤ p * 2 ^ L ∧
      p * 2 ^ L < 2 * 3 ^ (2 * (n + 1)) ∧ 3 * n ≤ L := by
  have hN : 3 ^ (2 * (n + 1)) = 9 ^ n * 9 := by
    rw [pow_mul, pow_succ]
    norm_num
  have hpow : 0 < (9 : ℕ) ^ n := by positivity
  have hpN : p < 3 ^ (2 * (n + 1)) := by
    rw [hN]
    nlinarith only [hp7, hpow]
  obtain ⟨L, hlow, hupp⟩ := dyadic_window p (3 ^ (2 * (n + 1))) (by omega) hpN
  refine ⟨L, hlow, hupp, ?_⟩
  by_contra hn
  have hL : L ≤ 3 * n := by omega
  have htwo : 2 ^ L ≤ (8 : ℕ) ^ n := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hL
    simpa only [pow_mul, show (2 : ℕ) ^ 3 = 8 by norm_num] using hh
  have hbound : 2 ^ L ≤ (9 : ℕ) ^ n :=
    htwo.trans (Nat.pow_le_pow_left (by decide : (8 : ℕ) ≤ 9) n)
  have hm := Nat.mul_le_mul hp7 hbound
  rw [hN] at hlow
  nlinarith only [hlow, hm, hpow]

theorem exponential_not_bounded_by_affine (c l a b : ℝ)
    (hc : 0 < c) (hl : 1 < l) :
    ¬ ∀ n : ℕ, c * l ^ n ≤ a + b * (n : ℝ) := by
  intro hbound
  let d := l - 1
  have hd : 0 < d := by dsimp [d]; linarith only [hl]
  let K := c * d ^ 2
  have hK : 0 < K := mul_pos hc (sq_pos_of_pos hd)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) ((|a| + 2 * |b|) / K))
  have hn1 : 1 < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hlarge : |a| + 2 * |b| < K * (n : ℝ) := by
    have hh := (div_lt_iff₀ hK).mp ((le_max_right _ _).trans_lt hn)
    simpa only [mul_comm] using hh
  have hbern := one_add_mul_sub_le_pow (by linarith only [hl] : -1 ≤ l) n
  have hp : (n : ℝ) * d ≤ l ^ n := by dsimp [d]; linarith only [hbern]
  have hs := mul_self_le_mul_self (mul_nonneg hn0.le hd.le) hp
  have hscaled := mul_le_mul_of_nonneg_left hs hc.le
  have hpower : l ^ (2 * n) = (l ^ n) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have hupper := hbound (2 * n)
  rw [hpower] at hupper
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hupper
  have hstrict := mul_lt_mul_of_pos_right hlarge hn0
  have ha := mul_le_mul_of_nonneg_right hn1.le (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity : 0 ≤ 2 * (n : ℝ))
  have hab : a + b * (2 * (n : ℝ)) ≤ (n : ℝ) * (|a| + 2 * |b|) := by
    nlinarith only [ha, hb, le_abs_self a]
  dsimp [K] at hstrict
  nlinarith only [hscaled, hupper, hstrict, hab]

end CollatzResearch.PositivePrefixArithmetic

#print axioms CollatzResearch.PositivePrefixArithmetic.dyadic_window
#print axioms CollatzResearch.PositivePrefixArithmetic.prefix_power_window
#print axioms CollatzResearch.PositivePrefixArithmetic.exponential_not_bounded_by_affine
