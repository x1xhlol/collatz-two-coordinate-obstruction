/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section5.NoHitOutput

/-!
# Section 5 Native No-Hit Rate

This leaf converts the checked raw no-hit error to an explicit polynomial
rate.  It uses the executable base-two logarithm ledger and contains no
finite-prefix patch or legacy endpoint adapter.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open Filter

/-- Both raw error terms are dominated by one common dyadic rate. -/
theorem taoSection5NoHitError_le_five_mul_two_rpow (B : ℕ) :
    taoSection5NoHitError B ≤
      5 * (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) := by
  let n := taoSection5N0 B
  have hideal :
      Real.exp (-((n : ℝ) / 3200)) ≤
        (2 : ℝ) ^ (-((n : ℝ) / 3200)) :=
    exp_neg_le_two_rpow_neg ((n : ℝ) / 3200) (by positivity)
  have hexponent :
      -((1 / 128 : ℝ) * (n : ℝ)) ≤ -((n : ℝ) / 3200) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hvaluationPow :
      (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) ≤
        (2 : ℝ) ^ (-((n : ℝ) / 3200)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  unfold taoSection5NoHitError
  dsimp [n] at hideal hvaluationPow ⊢
  calc
    Real.exp (-((taoSection5N0 B : ℝ) / 3200)) +
        4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
      (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) +
        4 * (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) :=
      add_le_add hideal (mul_le_mul_of_nonneg_left hvaluationPow (by norm_num))
    _ = 5 * (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) := by ring

/-- The base-two logarithm floor leaves at most one ten-step block. -/
theorem log_add_one_le_ten_mul_taoSection5N0_add_one (B : ℕ) :
    Nat.log 2 B + 1 ≤ 10 * (taoSection5N0 B + 1) := by
  have hdecomp := Nat.div_add_mod (Nat.log 2 B) 10
  have hrem := Nat.mod_lt (Nat.log 2 B) (by norm_num : 0 < 10)
  unfold taoSection5N0
  omega

/-- The common dyadic rate is at most twice the target polynomial rate for
every positive natural threshold. -/
theorem two_rpow_neg_n0_div_3200_le_two_mul_threshold_rpow
    {B : ℕ} (hB : 1 ≤ B) :
    (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) ≤
      2 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by
  let n := taoSection5N0 B
  have hnat : B < 2 ^ (10 * (n + 1)) :=
    (threshold_lt_two_pow_log_succ B).trans_le
      (Nat.pow_le_pow_right (by norm_num)
        (by simpa only [n] using log_add_one_le_ten_mul_taoSection5N0_add_one B))
  have hreal : (B : ℝ) < (2 : ℝ) ^ (10 * (n + 1) : ℕ) := by
    exact_mod_cast hnat
  have hneg := Real.rpow_lt_rpow_of_neg
    (by exact_mod_cast hB : 0 < (B : ℝ)) hreal
    (by norm_num : -(1 / 32000 : ℝ) < 0)
  have hleft :
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 3200)) <
        (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by
    calc
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 3200)) =
          (2 : ℝ) ^
            (((10 * (n + 1) : ℕ) : ℝ) * (-(1 / 32000 : ℝ))) := by
        congr 1
        push_cast
        ring
      _ = ((2 : ℝ) ^ (((10 * (n + 1) : ℕ) : ℝ))) ^
          (-(1 / 32000 : ℝ)) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
      _ = ((2 : ℝ) ^ (10 * (n + 1) : ℕ)) ^
          (-(1 / 32000 : ℝ)) := by
        rw [Real.rpow_natCast]
      _ < (B : ℝ) ^ (-(1 / 32000 : ℝ)) := hneg
  have hfactor :
      (2 : ℝ) ^ (1 / 3200 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (1 / 3200 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc
    (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) =
        (2 : ℝ) ^ (1 / 3200 : ℝ) *
          (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) / 3200)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      dsimp [n]
      congr 1
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ (1 / 3200 : ℝ) *
        (B : ℝ) ^ (-(1 / 32000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hleft.le
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor
        (Real.rpow_nonneg (Nat.cast_nonneg B) _)

theorem taoSection5NoHitError_nonneg (B : ℕ) :
    0 ≤ taoSection5NoHitError B := by
  unfold taoSection5NoHitError
  positivity

/-- Explicit source-facing polynomial rate, pointwise for every positive
natural threshold. -/
theorem taoSection5NoHitError_le_ten_mul_threshold_rpow
    {B : ℕ} (hB : 1 ≤ B) :
    taoSection5NoHitError B ≤
      10 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by
  calc
    taoSection5NoHitError B ≤
        5 * (2 : ℝ) ^ (-((taoSection5N0 B : ℝ) / 3200)) :=
      taoSection5NoHitError_le_five_mul_two_rpow B
    _ ≤ 5 * (2 * (B : ℝ) ^ (-(1 / 32000 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (two_rpow_neg_n0_div_3200_le_two_mul_threshold_rpow hB) (by norm_num)
    _ = 10 * (B : ℝ) ^ (-(1 / 32000 : ℝ)) := by ring

/-- Native no-hit output together with its explicit polynomial rate. -/
structure TaoSection5NoHitRateOutput (B : ℕ) : Prop where
  output : TaoSection5NoHitOutput B
  error_nonneg : 0 ≤ taoSection5NoHitError B
  error_le :
    taoSection5NoHitError B ≤
      10 * (B : ℝ) ^ (-(1 / 32000 : ℝ))

theorem TaoSection5NoHitRateOutput.of_output
    {B : ℕ} (output : TaoSection5NoHitOutput B) :
    TaoSection5NoHitRateOutput B :=
  { output := output
    error_nonneg := taoSection5NoHitError_nonneg B
    error_le := taoSection5NoHitError_le_ten_mul_threshold_rpow
      output.descent.one_le_B }

theorem eventually_taoSection5NoHitRateOutput :
    ∀ᶠ B : ℕ in atTop, TaoSection5NoHitRateOutput B :=
  eventually_taoSection5NoHitOutput.mono fun _ output =>
    TaoSection5NoHitRateOutput.of_output output

end

end Tao
end Erdos1135SecondScale
