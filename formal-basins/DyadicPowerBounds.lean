import OrbitPackingPowerRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CollatzCanonical.DyadicBounds

open CollatzOrbitPackingPowerRecurrence

/-- The floor of the base-two logarithm gives the exact dyadic interval for a positive integer. -/
theorem binaryLogFloor_bounds (n : ℕ) (hn : 1 ≤ n) :
    2 ^ binaryLogFloor n ≤ n ∧ n < 2 * 2 ^ binaryLogFloor n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor : (binaryLogFloor n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_natCast_nonneg n) hlog2.le)
  have hnext : Real.log (n : ℝ) / Real.log 2 < ((binaryLogFloor n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.log (n : ℝ) / Real.log 2))
  have hlo := Real.exp_le_exp.mpr ((le_div_iff₀ hlog2).mp hfloor)
  have hhi := Real.exp_lt_exp.mpr ((div_lt_iff₀ hlog2).mp hnext)
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hnpos] at hlo
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hnpos] at hhi
  refine ⟨?_, ?_⟩
  · exact_mod_cast hlo
  · have hh : n < 2 ^ (binaryLogFloor n + 1) := by exact_mod_cast hhi
    simpa only [pow_succ, Nat.mul_comm] using hh

/-- A dyadic lower bound controls every nonnegative power weight. -/
theorem two_power_le_real_power (X H : ℝ) (h : ℕ)
    (hX : (2 : ℝ) ^ h ≤ X) (hH : 0 ≤ H) :
    (2 : ℝ) ^ ((h : ℝ) * H) ≤ X ^ H := by
  rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.rpow_le_rpow (by positivity) hX hH

/-- The logarithmic base conversion used by the low-odd-count endpoint bound. -/
theorem three_real_power_eq_two_real_power (r : ℝ) :
    (3 : ℝ) ^ r = (2 : ℝ) ^ (r * Real.log 3 / Real.log 2) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp

/-- Low odd count gives a sublinear endpoint power whenever its exponent is below one. -/
theorem three_power_le_real_power (X ρ : ℝ) (h r : ℕ)
    (hX : (2 : ℝ) ^ h ≤ X) (hρ : 0 ≤ ρ) (hr : (r : ℝ) ≤ ρ * h) :
    (3 : ℝ) ^ r ≤ X ^ (ρ * Real.log 3 / Real.log 2) := by
  have hc : 0 ≤ ρ * Real.log 3 / Real.log 2 :=
    div_nonneg (mul_nonneg hρ (Real.log_nonneg (by norm_num)))
      (Real.log_nonneg (by norm_num))
  calc
    (3 : ℝ) ^ r = (3 : ℝ) ^ (r : ℝ) := (Real.rpow_natCast 3 r).symm
    _ ≤ (3 : ℝ) ^ (ρ * h) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr
    _ = (2 : ℝ) ^ ((h : ℝ) * (ρ * Real.log 3 / Real.log 2)) := by
      rw [three_real_power_eq_two_real_power]
      congr 1
      ring
    _ ≤ _ := two_power_le_real_power X (ρ * Real.log 3 / Real.log 2) h hX hc

/-- The corresponding bound with an explicitly floored odd-count cutoff. -/
theorem three_floor_power_le_real_power (X ρ : ℝ) (h : ℕ)
    (hX : (2 : ℝ) ^ h ≤ X) (hρ : 0 ≤ ρ) :
    (3 : ℝ) ^ Nat.floor (ρ * h) ≤ X ^ (ρ * Real.log 3 / Real.log 2) :=
  three_power_le_real_power X ρ h (Nat.floor (ρ * h)) hX hρ
    (Nat.floor_le (mul_nonneg hρ (Nat.cast_nonneg _)))

/-- The paper's logarithmic floor specializes the generic low-count power bound. -/
theorem three_power_le_nat_power (n r : ℕ) (ρ : ℝ) (hn : 1 ≤ n) (hρ : 0 ≤ ρ)
    (hr : (r : ℝ) ≤ ρ * binaryLogFloor n) :
    (3 : ℝ) ^ r ≤ (n : ℝ) ^ (ρ * Real.log 3 / Real.log 2) := by
  have hdyad : (2 : ℝ) ^ binaryLogFloor n ≤ (n : ℝ) := by
    exact_mod_cast (binaryLogFloor_bounds n hn).1
  exact three_power_le_real_power n ρ (binaryLogFloor n) r hdyad hρ hr

/-- The paper's logarithmic floor also controls the entropy weight. -/
theorem two_power_le_nat_power (n : ℕ) (H : ℝ) (hn : 1 ≤ n) (hH : 0 ≤ H) :
    (2 : ℝ) ^ ((binaryLogFloor n : ℝ) * H) ≤ (n : ℝ) ^ H := by
  have hdyad : (2 : ℝ) ^ binaryLogFloor n ≤ (n : ℝ) := by
    exact_mod_cast (binaryLogFloor_bounds n hn).1
  exact two_power_le_real_power n H (binaryLogFloor n) hdyad hH

end CollatzCanonical.DyadicBounds
