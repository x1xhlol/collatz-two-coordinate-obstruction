/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Mathlib.Tactic

/-!
# Section 5 Five-Step Exponent Compression

This leaf isolates the natural-number compression behind the deterministic
Section 5 descent estimate.  It compares each five powers of `3` with eight
powers of `2` and turns the inclusive high-weight cutoff into a strict
integral exponent gap.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Five powers of `3` fit below eight powers of `2`, with a coarse
two-bit bound for each remainder step. -/
theorem three_pow_five_mul_add_le_two_pow_eight_mul_add (q r : ℕ) :
    3 ^ (5 * q + r) ≤ 2 ^ (8 * q + 2 * r) := by
  have hbase : (3 : ℕ) ^ 5 < 2 ^ 8 := by norm_num
  have hblocks : 3 ^ (5 * q) ≤ 2 ^ (8 * q) := by
    have h := Nat.pow_le_pow_left hbase.le q
    simpa only [← Nat.pow_mul] using h
  have hrem : 3 ^ r ≤ 2 ^ (2 * r) := by
    have h := Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ≤ 2 ^ 2) r
    simpa only [← Nat.pow_mul] using h
  calc
    3 ^ (5 * q + r) = 3 ^ (5 * q) * 3 ^ r := by rw [Nat.pow_add]
    _ ≤ 2 ^ (8 * q) * 2 ^ (2 * r) := Nat.mul_le_mul hblocks hrem
    _ = 2 ^ (8 * q + 2 * r) := by rw [Nat.pow_add]

/-- The inclusive source cutoff still leaves a strict quotient-sized exponent
gap once at least one five-step block is present. -/
theorem five_step_exponent_add_quotient_lt
    {n q r e w : ℕ}
    (hn : n = 5 * q + r) (hr : r < 5) (hn5 : 5 ≤ n)
    (he : e = 8 * q + 2 * r) (hweight : 19 * n ≤ 10 * w) :
    e + q < w := by
  have hq : 1 ≤ q := by omega
  have hstrict : 10 * (e + q) < 19 * n := by omega
  have hscaled : 10 * (e + q) < 10 * w := hstrict.trans_le hweight
  omega

/-- Integral form of the strict exponent gap. -/
theorem five_step_exponent_add_quotient_succ_le
    {n q r e w : ℕ}
    (hn : n = 5 * q + r) (hr : r < 5) (hn5 : 5 ≤ n)
    (he : e = 8 * q + 2 * r) (hweight : 19 * n ≤ 10 * w) :
    e + q + 1 ≤ w :=
  Nat.succ_le_iff.mpr
    (five_step_exponent_add_quotient_lt hn hr hn5 he hweight)

/-- Combined power and strict-gap packet for a five-step decomposition. -/
theorem nat_five_step_compression
    {n q r e w : ℕ}
    (hn : n = 5 * q + r) (hr : r < 5) (hn5 : 5 ≤ n)
    (he : e = 8 * q + 2 * r) (hweight : 19 * n ≤ 10 * w) :
    3 ^ n ≤ 2 ^ e ∧ e + q + 1 ≤ w := by
  subst n
  subst e
  exact
    ⟨three_pow_five_mul_add_le_two_pow_eight_mul_add q r,
      five_step_exponent_add_quotient_succ_le rfl hr hn5 rfl hweight⟩

/-- Direct quotient/remainder form of the five-step power comparison. -/
theorem three_pow_le_two_pow_fiveStep (n : ℕ) :
    3 ^ n ≤ 2 ^ (8 * (n / 5) + 2 * (n % 5)) := by
  have hdecomp := Nat.div_add_mod n 5
  have hn : n = 5 * (n / 5) + n % 5 := by omega
  calc
    3 ^ n = 3 ^ (5 * (n / 5) + n % 5) :=
      congrArg (fun k : ℕ => 3 ^ k) hn
    _ ≤ 2 ^ (8 * (n / 5) + 2 * (n % 5)) :=
      three_pow_five_mul_add_le_two_pow_eight_mul_add (n / 5) (n % 5)

/-- Direct Section 5 weight-gap wrapper at the natural quotient and
remainder. -/
theorem fiveStep_weight_gap
    {n w : ℕ} (hn : 5 ≤ n) (hweight : 19 * n ≤ 10 * w) :
    8 * (n / 5) + 2 * (n % 5) + n / 5 + 1 ≤ w := by
  have hdecomp := Nat.div_add_mod n 5
  have hnDecomp : n = 5 * (n / 5) + n % 5 := by omega
  exact five_step_exponent_add_quotient_succ_le hnDecomp
    (Nat.mod_lt n (by norm_num)) hn rfl hweight

/-- The five-step power and integral gap produce the rational denominator
gain used by deterministic descent. -/
theorem three_pow_div_two_pow_le_fiveStep
    {n w : ℕ} (hn : 5 ≤ n) (hweight : 19 * n ≤ 10 * w) :
    (3 : ℚ) ^ n / (2 : ℚ) ^ w ≤
      1 / (2 : ℚ) ^ (n / 5 + 1) := by
  let e := 8 * (n / 5) + 2 * (n % 5)
  have hpowerNat : 3 ^ n ≤ 2 ^ e := by
    simpa only [e] using three_pow_le_two_pow_fiveStep n
  have hgap : e + (n / 5 + 1) ≤ w := by
    have h := fiveStep_weight_gap hn hweight
    dsimp [e]
    omega
  have hpower : (3 : ℚ) ^ n ≤ (2 : ℚ) ^ e := by
    exact_mod_cast hpowerNat
  have htwoPowNat : 2 ^ (e + (n / 5 + 1)) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by norm_num) hgap
  have htwoPow :
      (2 : ℚ) ^ (e + (n / 5 + 1)) ≤ (2 : ℚ) ^ w := by
    exact_mod_cast htwoPowNat
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    (3 : ℚ) ^ n * (2 : ℚ) ^ (n / 5 + 1) ≤
        (2 : ℚ) ^ e * (2 : ℚ) ^ (n / 5 + 1) :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = (2 : ℚ) ^ (e + (n / 5 + 1)) :=
      (pow_add (2 : ℚ) e (n / 5 + 1)).symm
    _ ≤ (2 : ℚ) ^ w := htwoPow
    _ = 1 * (2 : ℚ) ^ w := by ring

end Tao
end Erdos1135SecondScale
