import Erdos1135.NumberTheory.Rhin.Statement
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.Parity

/-!
# Elementary logarithmic and rounding facts for the Rhin specialization

This number-theory-only layer defines the phase quantity independently of the
ND namespace.  Besides the logarithmic ratio bounds used to control Rhin's
height, it proves the elementary nonvanishing argument consumed by finite
absorption.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

/-- `log_2 3`, kept in the number-theory layer until the narrow ND adapter. -/
def logTwoThree : ℝ :=
  Real.log 3 / Real.log 2

/-- Distance to Mathlib's nearest integer, with ties rounded upward. -/
def nearestIntegerNorm (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

/-- The eventual phase-power-law surface produced by specializing Rhin's
three-integer linear form. -/
def LargeFrequencyPhaseBound : Prop :=
  ∃ factor : ℝ, 0 < factor ∧
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ q : ℕ, threshold ≤ q →
        factor * Real.rpow (q : ℝ) (-(133 / 10 : ℝ)) ≤
          nearestIntegerNorm ((q : ℝ) * logTwoThree)

theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

theorem one_lt_logTwoThree : 1 < logTwoThree := by
  have hlog : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  rw [logTwoThree, one_lt_div log_two_pos]
  exact hlog

theorem logTwoThree_lt_two : logTwoThree < 2 := by
  have hlog : Real.log 3 < Real.log 4 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log (2 * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 :=
        Real.log_mul (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by ring
  rw [logTwoThree, div_lt_iff₀ log_two_pos]
  linarith

/-- For frequencies at least two, nearest-integer specialization increases
Rhin's height by at most the fixed factor three.  The coarse factor is
intentional: G8a needs positivity, not an optimized constant. -/
theorem roundLogHeight_le_three_mul
    {q : ℕ} (hq : 2 ≤ q) :
    linearFormHeight
        (-(round ((q : ℝ) * logTwoThree))) (q : ℤ) ≤
      3 * q := by
  let x : ℝ := (q : ℝ) * logTwoThree
  let p : ℤ := round x
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hxLower : (1 : ℝ) < x := by
    dsimp only [x]
    have hratio := one_lt_logTwoThree
    nlinarith
  have hxUpper : x < 2 * (q : ℝ) := by
    dsimp only [x]
    have hratio := logTwoThree_lt_two
    nlinarith
  have hpPosReal : (0 : ℝ) < (p : ℤ) := by
    have hround := sub_half_lt_round x
    change x - 1 / 2 < (p : ℤ) at hround
    linarith
  have hpNonneg : 0 ≤ p := by
    exact_mod_cast hpPosReal.le
  have hpLeReal : (p : ℝ) ≤ 3 * (q : ℝ) := by
    have hround := round_le_add_half x
    change (p : ℝ) ≤ x + 1 / 2 at hround
    linarith
  have hpLeInt : p ≤ (3 * q : ℕ) := by
    exact_mod_cast hpLeReal
  have hpNatAbs : p.natAbs ≤ 3 * q := by
    rw [← Int.ofNat_le, Int.natAbs_of_nonneg hpNonneg]
    exact hpLeInt
  change max (-p).natAbs ((q : ℤ).natAbs) ≤ 3 * q
  apply max_le
  · simpa only [Int.natAbs_neg] using hpNatAbs
  · simp only [Int.natAbs_natCast]
    omega

/-- The specialized linear form is `log 2` times the nearest-integer phase
difference. -/
theorem abs_linearForm_round_eq
    (q : ℕ) :
    |linearForm 0 (-(round ((q : ℝ) * logTwoThree))) (q : ℤ)| =
      Real.log 2 * nearestIntegerNorm ((q : ℝ) * logTwoThree) := by
  have hlogTwoNe : Real.log 2 ≠ 0 := log_two_pos.ne'
  have hform :
      linearForm 0 (-(round ((q : ℝ) * logTwoThree))) (q : ℤ) =
        Real.log 2 *
          ((q : ℝ) * logTwoThree -
            (round ((q : ℝ) * logTwoThree) : ℝ)) := by
    unfold linearForm logTwoThree
    push_cast
    field_simp [hlogTwoNe]
    ring
  rw [hform, abs_mul, abs_of_pos log_two_pos]
  rfl

private theorem three_pow_ne_two_pow
    {q n : ℕ} (hn : 0 < n) :
    3 ^ q ≠ 2 ^ n := by
  intro h
  have hOdd : Odd (3 ^ q) :=
    Odd.pow (⟨1, by norm_num⟩ : Odd (3 : ℕ))
  have hEven : Even (2 ^ n) :=
    (show Even (2 : ℕ) by norm_num).pow_of_ne_zero hn.ne'
  rw [h] at hOdd
  exact (Nat.not_odd_iff_even.mpr hEven) hOdd

/-- No positive-frequency integer linear form `q log 3 - p log 2`
vanishes.  The proof converts a hypothetical equality to `3^q = 2^n` and
uses parity. -/
theorem logLinearForm_ne_zero
    (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (q : ℝ) * Real.log 3 - (p : ℝ) * Real.log 2 ≠ 0 := by
  intro hzero
  have hlogs :
      (q : ℝ) * Real.log 3 = (p : ℝ) * Real.log 2 := by
    linarith
  have hleft : 0 < (q : ℝ) * Real.log 3 :=
    mul_pos (Nat.cast_pos.mpr hq) (Real.log_pos (by norm_num))
  have hpMul : 0 < (p : ℝ) * Real.log 2 := by
    rw [← hlogs]
    exact hleft
  have hpReal : 0 < (p : ℝ) :=
    (mul_pos_iff_of_pos_right log_two_pos).mp hpMul
  have hp : 0 < p := by
    exact_mod_cast hpReal
  let n : ℕ := p.natAbs
  have hn : 0 < n := by
    dsimp only [n]
    exact Int.natAbs_pos.mpr hp.ne'
  have hpNatAbs : (p : ℝ) = (n : ℝ) := by
    dsimp only [n]
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hp.le]
  have hlogPowers :
      Real.log ((3 : ℝ) ^ q) = Real.log ((2 : ℝ) ^ n) := by
    rw [Real.log_pow, Real.log_pow]
    simpa only [hpNatAbs] using hlogs
  have hpowReal : (3 : ℝ) ^ q = (2 : ℝ) ^ n :=
    Real.log_injOn_pos
      (pow_pos (by norm_num : (0 : ℝ) < 3) q)
      (pow_pos (by norm_num : (0 : ℝ) < 2) n)
      hlogPowers
  have hpowNat : 3 ^ q = 2 ^ n := by
    exact_mod_cast hpowReal
  exact three_pow_ne_two_pow hn hpowNat

/-- A positive multiple of `log_2 3` is never an integer. -/
theorem nat_mul_logTwoThree_ne_int
    (q : ℕ) (hq : 0 < q) (p : ℤ) :
    (q : ℝ) * logTwoThree ≠ (p : ℝ) := by
  intro h
  apply logLinearForm_ne_zero p hq
  have h' := h
  unfold logTwoThree at h'
  field_simp [log_two_pos.ne'] at h'
  linarith

/-- Every positive-frequency nearest-integer phase gap is strictly positive. -/
theorem nearestIntegerNorm_mul_logTwoThree_pos
    (q : ℕ) (hq : 0 < q) :
    0 < nearestIntegerNorm ((q : ℝ) * logTwoThree) := by
  rw [nearestIntegerNorm, abs_pos, sub_ne_zero]
  exact nat_mul_logTwoThree_ne_int q hq (round ((q : ℝ) * logTwoThree))

end

end Rhin
end NumberTheory
end Erdos1135
