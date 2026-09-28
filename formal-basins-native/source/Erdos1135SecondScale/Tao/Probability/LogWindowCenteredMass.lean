/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.LogWindowBoundaryMass

/-!
# Centered Harmonic Mass Of Odd Windows

This neutral leaf centers the logarithmic mass of an odd natural interval at
one half of its endpoint log-ratio.  The proof uses the exact odd/even
harmonic decomposition, so the leading constant retains the parity factor.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

private theorem log_natCast_le_logMass_centered (n : ℕ) :
    Real.log (n : ℝ) ≤ logMass n := by
  by_cases hn : n = 0
  · simp [hn, logMass]
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [logMass_eq_harmonic]
  calc
    Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn hnPos
      · show (0 : ℝ) < (n + 1 : ℕ)
        positivity
      · exact_mod_cast Nat.le_succ n
    _ ≤ harmonic n := log_add_one_le_harmonic n

private theorem logMass_le_one_add_log_natCast_centered (n : ℕ) :
    logMass n ≤ 1 + Real.log (n : ℝ) := by
  rw [logMass_eq_harmonic]
  exact harmonic_le_one_add_log n

/-- The mass of an odd interval differs from one half of its endpoint
log-ratio by at most a universal rounding constant. -/
theorem abs_logFinsetMass_oddLogWindow_sub_half_log_ratio_le_three_halves
    {a b : ℕ} (ha : 4 ≤ a) (hab : a ≤ b) :
    |logFinsetMass (oddLogWindow a b) -
        (1 / 2 : ℝ) * (Real.log (b : ℝ) - Real.log (a : ℝ))| ≤
      3 / 2 := by
  let P := (a - 1) / 2
  let C := b / 2
  have haNatPos : 0 < a := by omega
  have hbNatPos : 0 < b := haNatPos.trans_le hab
  have hPNatPos : 0 < P := by
    dsimp [P]
    omega
  have hCNatPos : 0 < C := by
    dsimp [C]
    omega
  have haPos : (0 : ℝ) < a := by exact_mod_cast haNatPos
  have hbPos : (0 : ℝ) < b := by exact_mod_cast hbNatPos
  have hPPos : (0 : ℝ) < P := by exact_mod_cast hPNatPos
  have hCPos : (0 : ℝ) < C := by exact_mod_cast hCNatPos
  have hPonePos : (0 : ℝ) < (P + 1 : ℕ) := by positivity
  have hConePos : (0 : ℝ) < (C + 1 : ℕ) := by positivity
  have hfullLower :
      Real.log (b : ℝ) - Real.log (a : ℝ) - 1 ≤
        logMass b - logMass (a - 1) := by
    have hbLower := log_natCast_le_logMass_centered b
    have haUpper := logMass_le_one_add_log_natCast_centered (a - 1)
    have hlogSub : Real.log ((a - 1 : ℕ) : ℝ) ≤ Real.log (a : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (a - 1 : ℕ)
        exact_mod_cast (show 0 < a - 1 by omega)
      · exact haPos
      · exact_mod_cast (show a - 1 ≤ a by omega)
    nlinarith
  have hfullUpper :
      logMass b - logMass (a - 1) ≤
        Real.log (b : ℝ) - Real.log (a : ℝ) + 1 := by
    have hbUpper := logMass_le_one_add_log_natCast_centered b
    have haLower : Real.log (a : ℝ) ≤ logMass (a - 1) := by
      rw [logMass_eq_harmonic]
      simpa only [Nat.sub_add_cancel (show 1 ≤ a by omega)] using
        log_add_one_le_harmonic (a - 1)
    nlinarith
  have hlogBLe :
      Real.log (b : ℝ) ≤
        Real.log 2 + Real.log ((C + 1 : ℕ) : ℝ) := by
    have hbLeNat : b ≤ 2 * (C + 1) := by
      dsimp [C]
      omega
    have hmono :
        Real.log (b : ℝ) ≤ Real.log ((2 * (C + 1) : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn hbPos
      · show (0 : ℝ) < (2 * (C + 1) : ℕ)
        positivity
      · exact_mod_cast hbLeNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hConePos.ne'] using hmono
  have hlogPLeA :
      Real.log 2 + Real.log (P : ℝ) ≤ Real.log (a : ℝ) := by
    have hPLeNat : 2 * P ≤ a := by
      dsimp [P]
      omega
    have hmono : Real.log ((2 * P : ℕ) : ℝ) ≤ Real.log (a : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (2 * P : ℕ)
        exact_mod_cast (show 0 < 2 * P by omega)
      · exact haPos
      · exact_mod_cast hPLeNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPPos.ne'] using hmono
  have hratioLeEven :
      Real.log (b : ℝ) - Real.log (a : ℝ) ≤
        Real.log ((C + 1 : ℕ) : ℝ) - Real.log (P : ℝ) := by
    linarith [hlogBLe, hlogPLeA]
  have hevenLower :
      Real.log (b : ℝ) - Real.log (a : ℝ) - 1 ≤
        logMass C - logMass P := by
    have hCLower : Real.log ((C + 1 : ℕ) : ℝ) ≤ logMass C := by
      rw [logMass_eq_harmonic]
      exact log_add_one_le_harmonic C
    have hPUpper := logMass_le_one_add_log_natCast_centered P
    nlinarith [hratioLeEven]
  have hlogCLeB :
      Real.log 2 + Real.log (C : ℝ) ≤ Real.log (b : ℝ) := by
    have hCLeNat : 2 * C ≤ b := by
      dsimp [C]
      omega
    have hmono : Real.log ((2 * C : ℕ) : ℝ) ≤ Real.log (b : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (2 * C : ℕ)
        exact_mod_cast (show 0 < 2 * C by omega)
      · exact hbPos
      · exact_mod_cast hCLeNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hCPos.ne'] using hmono
  have hlogALe :
      Real.log (a : ℝ) ≤
        Real.log 2 + Real.log ((P + 1 : ℕ) : ℝ) := by
    have haLeNat : a ≤ 2 * (P + 1) := by
      dsimp [P]
      omega
    have hmono :
        Real.log (a : ℝ) ≤ Real.log ((2 * (P + 1) : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn haPos
      · show (0 : ℝ) < (2 * (P + 1) : ℕ)
        positivity
      · exact_mod_cast haLeNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPonePos.ne'] using hmono
  have hevenRatioLe :
      Real.log (C : ℝ) - Real.log ((P + 1 : ℕ) : ℝ) ≤
        Real.log (b : ℝ) - Real.log (a : ℝ) := by
    linarith [hlogCLeB, hlogALe]
  have hevenUpper :
      logMass C - logMass P ≤
        Real.log (b : ℝ) - Real.log (a : ℝ) + 1 := by
    have hCUpper := logMass_le_one_add_log_natCast_centered C
    have hPLower : Real.log ((P + 1 : ℕ) : ℝ) ≤ logMass P := by
      rw [logMass_eq_harmonic]
      exact log_add_one_le_harmonic P
    nlinarith [hevenRatioLe]
  rw [logFinsetMass_oddLogWindow_eq_harmonic_difference
    (by omega : 1 ≤ a) hab]
  apply abs_le.mpr
  constructor <;> dsimp [P, C] at * <;> nlinarith

/-- Rounding both endpoints of a real power window costs at most one further
unit after applying the centered odd-window estimate. -/
theorem abs_rounded_power_oddWindow_mass_sub_half_log_width_le_five_halves
    {y alpha : ℝ} (hy : 4 ≤ y) (halpha : 1 < alpha)
    (hab : Nat.ceil y ≤ Nat.floor (Real.rpow y alpha)) :
    |logFinsetMass
          (oddLogWindow (Nat.ceil y) (Nat.floor (Real.rpow y alpha))) -
        (1 / 2 : ℝ) * ((alpha - 1) * Real.log y)| ≤
      5 / 2 := by
  let a := Nat.ceil y
  let z := Real.rpow y alpha
  let b := Nat.floor z
  have hyPos : 0 < y := by linarith
  have hzPos : 0 < z := by
    dsimp [z]
    exact Real.rpow_pos_of_pos hyPos _
  have hyLeZ : y ≤ z := by
    dsimp [z]
    exact Real.self_le_rpow_of_one_le (by linarith) halpha.le
  have haReal : y ≤ (a : ℝ) := by
    dsimp [a]
    exact Nat.le_ceil y
  have haUpper : (a : ℝ) ≤ 2 * y := by
    have hceil := Nat.ceil_lt_add_one hyPos.le
    dsimp [a]
    linarith
  have haNat : 4 ≤ a := by exact_mod_cast hy.trans haReal
  have hbLower : z / 2 ≤ (b : ℝ) := by
    have hfloor := Nat.lt_floor_add_one z
    dsimp [b]
    nlinarith [hyLeZ, hy]
  have hbUpper : (b : ℝ) ≤ z := by
    dsimp [b]
    exact Nat.floor_le hzPos.le
  have hbPos : (0 : ℝ) < b := by nlinarith [hbLower, hzPos]
  have haPos : (0 : ℝ) < a := by positivity
  have hlogALower : Real.log y ≤ Real.log (a : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hyPos haPos haReal
  have hlogAUpper : Real.log (a : ℝ) ≤ Real.log 2 + Real.log y := by
    have hmono := Real.strictMonoOn_log.monotoneOn haPos
      (mul_pos (by norm_num) hyPos) haUpper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne'] at hmono
    exact hmono
  have hlogBLower : alpha * Real.log y - Real.log 2 ≤ Real.log (b : ℝ) := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (div_pos hzPos (by norm_num)) hbPos hbLower
    rw [Real.log_div hzPos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    have hlogZ : Real.log z = alpha * Real.log y := by
      dsimp [z]
      exact Real.log_rpow hyPos _
    rw [hlogZ] at hmono
    exact hmono
  have hlogBUpper : Real.log (b : ℝ) ≤ alpha * Real.log y := by
    have hmono := Real.strictMonoOn_log.monotoneOn hbPos hzPos hbUpper
    have hlogZ : Real.log z = alpha * Real.log y := by
      dsimp [z]
      exact Real.log_rpow hyPos _
    rwa [hlogZ] at hmono
  have hlogTwoLt : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hratio :
      |(Real.log (b : ℝ) - Real.log (a : ℝ)) -
          (alpha - 1) * Real.log y| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hlogALower, hlogAUpper,
      hlogBLower, hlogBUpper, hlogTwoLt]
  have hmass :=
    abs_logFinsetMass_oddLogWindow_sub_half_log_ratio_le_three_halves
      haNat hab
  have hrearrange :
      logFinsetMass (oddLogWindow a b) -
          (1 / 2 : ℝ) * ((alpha - 1) * Real.log y) =
        (logFinsetMass (oddLogWindow a b) -
          (1 / 2 : ℝ) * (Real.log (b : ℝ) - Real.log (a : ℝ))) +
        (1 / 2 : ℝ) *
          ((Real.log (b : ℝ) - Real.log (a : ℝ)) -
            (alpha - 1) * Real.log y) := by ring
  rw [show Nat.ceil y = a by rfl, show Nat.floor (Real.rpow y alpha) = b by rfl]
  rw [hrearrange]
  calc
    |_ + _| ≤
        |logFinsetMass (oddLogWindow a b) -
          (1 / 2 : ℝ) * (Real.log (b : ℝ) - Real.log (a : ℝ))| +
        |(1 / 2 : ℝ) *
          ((Real.log (b : ℝ) - Real.log (a : ℝ)) -
            (alpha - 1) * Real.log y)| := abs_add_le _ _
    _ ≤ 3 / 2 + (1 / 2 : ℝ) * 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add hmass (mul_le_mul_of_nonneg_left hratio (by norm_num))
    _ = 5 / 2 := by norm_num

end

end Tao
end Erdos1135SecondScale
