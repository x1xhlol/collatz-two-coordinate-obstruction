import Erdos1135.Tao.Probability.LogWindowOddPrefix
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic Mass of Odd Window Boundaries

This neutral leaf proves exact odd-prefix and odd-window identities before
bounding multiplicative endpoint strips. It contains no Section 5 schedule,
PMF, or passage-event definitions.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

/-- Exact harmonic decomposition into odd and even positive integers. -/
theorem logFinsetMass_oddLogWindow_one_eq_logMass_sub_half (X : ℕ) :
    logFinsetMass (oddLogWindow 1 X) =
      logMass X - (1 / 2 : ℝ) * logMass (X / 2) := by
  rw [← logCount_oddLogWindowSet_eq_logFinsetMass]
  induction X with
  | zero => simp [logCount, logMass]
  | succ X ih =>
      by_cases hodd : (X + 1) % 2 = 1
      · rw [logCount_oddLogWindowSet_one_succ_of_odd hodd, logMass_succ]
        have hdiv : (X + 1) / 2 = X / 2 := by omega
        rw [hdiv]
        linarith
      · rw [logCount_oddLogWindowSet_one_succ_of_even hodd, logMass_succ]
        have hdiv : (X + 1) / 2 = X / 2 + 1 := by omega
        let k := X / 2
        have hX : X = 2 * k + 1 := by
          dsimp [k]
          omega
        have hweight :
            logWeight X = (1 / 2 : ℝ) * logWeight (X / 2) := by
          calc
            logWeight X = logWeight (2 * k + 1) := by rw [hX]
            _ = (1 / 2 : ℝ) * logWeight k := by
              unfold logWeight
              push_cast
              field_simp
              ring
            _ = (1 / 2 : ℝ) * logWeight (X / 2) := by rfl
        rw [hdiv, logMass_succ, hweight]
        linarith

/-- An odd natural window is the difference of two odd prefixes. -/
theorem logFinsetMass_oddLogWindow_eq_sub_prefix
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    logFinsetMass (oddLogWindow a b) =
      logFinsetMass (oddLogWindow 1 b) -
        logFinsetMass (oddLogWindow 1 (a - 1)) := by
  have hunion :
      oddLogWindow 1 b =
        oddLogWindow 1 (a - 1) ∪ oddLogWindow a b := by
    ext n
    simp only [oddLogWindow_mem, Finset.mem_union]
    omega
  have hdisjoint :
      Disjoint (oddLogWindow 1 (a - 1)) (oddLogWindow a b) := by
    rw [Finset.disjoint_left]
    intro n hnLow hnHigh
    rw [oddLogWindow_mem] at hnLow hnHigh
    omega
  unfold logFinsetMass
  rw [hunion, Finset.sum_union hdisjoint]
  ring

/-- Exact odd-window mass as a difference of harmonic and even-prefix masses. -/
theorem logFinsetMass_oddLogWindow_eq_harmonic_difference
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    logFinsetMass (oddLogWindow a b) =
      (logMass b - logMass (a - 1)) -
        (1 / 2 : ℝ) * (logMass (b / 2) - logMass ((a - 1) / 2)) := by
  rw [logFinsetMass_oddLogWindow_eq_sub_prefix ha hab,
    logFinsetMass_oddLogWindow_one_eq_logMass_sub_half,
    logFinsetMass_oddLogWindow_one_eq_logMass_sub_half]
  ring

private theorem log_natCast_le_logMass (n : ℕ) :
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
      exact_mod_cast Nat.le_succ n
    _ ≤ harmonic n := log_add_one_le_harmonic n

private theorem logMass_le_one_add_log_natCast (n : ℕ) :
    logMass n ≤ 1 + Real.log (n : ℝ) := by
  rw [logMass_eq_harmonic]
  exact harmonic_le_one_add_log n

private theorem log_two_lt_one_boundary : Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

/-- Forgetting parity costs at most one additive unit beyond the logarithmic
endpoint ratio. -/
theorem logFinsetMass_oddLogWindow_le_log_ratio_add_one
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    logFinsetMass (oddLogWindow a b) ≤
      1 + Real.log (b : ℝ) - Real.log (a : ℝ) := by
  have hevenNonneg :
      0 ≤ logMass (b / 2) - logMass ((a - 1) / 2) := by
    exact sub_nonneg.mpr (logMass_mono (by omega))
  have hbUpper := logMass_le_one_add_log_natCast b
  have haLower : Real.log (a : ℝ) ≤ logMass (a - 1) := by
    rw [logMass_eq_harmonic]
    simpa only [Nat.sub_add_cancel ha] using log_add_one_le_harmonic (a - 1)
  rw [logFinsetMass_oddLogWindow_eq_harmonic_difference ha hab]
  nlinarith

/-- The odd part of a natural interval retains half of its logarithmic ratio,
up to a uniform rounding constant. -/
theorem half_log_ratio_sub_two_le_logFinsetMass_oddLogWindow
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (1 / 2 : ℝ) * (Real.log (b : ℝ) - Real.log (a : ℝ)) - 2 ≤
      logFinsetMass (oddLogWindow a b) := by
  let A := (a - 1) / 2
  let C := b / 2
  have haNatPos : 0 < a := by omega
  have hbNatPos : 0 < b := by omega
  have haPos : (0 : ℝ) < a := by exact_mod_cast haNatPos
  have hbPos : (0 : ℝ) < b := by exact_mod_cast hbNatPos
  have hAPos : (0 : ℝ) < (A + 1 : ℕ) := by positivity
  have hCnatPos : 0 < C := by
    dsimp [C]
    omega
  have hCPos : (0 : ℝ) < C := by exact_mod_cast hCnatPos
  have hhalfPos : (0 : ℝ) < (a : ℝ) / 2 := by positivity
  have hhalfLe : (a : ℝ) / 2 ≤ (A + 1 : ℕ) := by
    have hnat : a ≤ 2 * (A + 1) := by
      dsimp [A]
      omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hnatReal : (a : ℝ) ≤ (2 * (A + 1) : ℕ) := by exact_mod_cast hnat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hnatReal
  have hlogHalfLe :
      Real.log ((a : ℝ) / 2) ≤ Real.log ((A + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hhalfPos hAPos hhalfLe
  rw [Real.log_div haPos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogHalfLe
  have hlogCLe : Real.log (C : ℝ) ≤ Real.log (b : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn hCPos hbPos
    exact_mod_cast Nat.div_le_self b 2
  have hfullLower :
      Real.log (b : ℝ) - (1 + Real.log (a : ℝ)) ≤
        logMass b - logMass (a - 1) := by
    have hbLower := log_natCast_le_logMass b
    have haUpper := logMass_le_one_add_log_natCast (a - 1)
    have hlogAMono : Real.log ((a - 1 : ℕ) : ℝ) ≤ Real.log (a : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (a - 1 : ℕ)
        exact_mod_cast (show 0 < a - 1 by omega)
      · exact haPos
      · exact_mod_cast (show a - 1 ≤ a by omega)
    nlinarith
  have hevenUpper :
      logMass (b / 2) - logMass ((a - 1) / 2) ≤
        2 + Real.log (b : ℝ) - Real.log (a : ℝ) := by
    change logMass C - logMass A ≤ _
    have hCUpper := logMass_le_one_add_log_natCast C
    have hALower : Real.log ((A + 1 : ℕ) : ℝ) ≤ logMass A := by
      rw [logMass_eq_harmonic]
      exact log_add_one_le_harmonic A
    nlinarith [hlogHalfLe, hlogCLe, log_two_lt_one_boundary]
  rw [logFinsetMass_oddLogWindow_eq_harmonic_difference
    (by omega : 1 ≤ a) hab]
  nlinarith

/-- A rounded power window has mass linear in its logarithmic width once that
width absorbs the two endpoint losses. -/
theorem one_eighth_log_width_le_rounded_power_oddWindow_mass
    {y alpha : ℝ} (hy : 2 ≤ y) (halpha : 1 < alpha)
    (hab : Nat.ceil y ≤ Nat.floor (Real.rpow y alpha))
    (hwidth : 8 ≤ (alpha - 1) * Real.log y) :
    ((alpha - 1) / 8) * Real.log y ≤
      logFinsetMass
        (oddLogWindow (Nat.ceil y) (Nat.floor (Real.rpow y alpha))) := by
  let a := Nat.ceil y
  let z := Real.rpow y alpha
  let b := Nat.floor z
  have hyPos : 0 < y := by linarith
  have hyOne : 1 ≤ y := by linarith
  have hzPos : 0 < z := by
    dsimp [z]
    exact Real.rpow_pos_of_pos hyPos _
  have hyLeZ : y ≤ z := by
    dsimp [z]
    exact Real.self_le_rpow_of_one_le hyOne halpha.le
  have haReal : y ≤ (a : ℝ) := by
    dsimp [a]
    exact Nat.le_ceil y
  have haUpper : (a : ℝ) ≤ 2 * y := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ y)
    dsimp [a]
    nlinarith
  have haNat : 2 ≤ a := by
    exact_mod_cast hy.trans haReal
  have hbLower : z / 2 ≤ (b : ℝ) := by
    have hfloor := Nat.lt_floor_add_one z
    dsimp [b]
    nlinarith [hyLeZ, hy]
  have hbPos : (0 : ℝ) < b := by
    nlinarith [hbLower, hzPos]
  have haPos : (0 : ℝ) < a := by positivity
  have hlogA : Real.log (a : ℝ) ≤ Real.log 2 + Real.log y := by
    have hmono := Real.strictMonoOn_log.monotoneOn haPos
      (mul_pos (by norm_num) hyPos) haUpper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne'] at hmono
    exact hmono
  have hlogB : alpha * Real.log y - Real.log 2 ≤ Real.log (b : ℝ) := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (div_pos hzPos (by norm_num)) hbPos hbLower
    rw [Real.log_div hzPos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    have hlogZ : Real.log z = alpha * Real.log y := by
      dsimp [z]
      exact Real.log_rpow hyPos _
    rw [hlogZ] at hmono
    exact hmono
  have hnatural :=
    half_log_ratio_sub_two_le_logFinsetMass_oddLogWindow haNat hab
  have hgap :
      (alpha - 1) * Real.log y - 2 * Real.log 2 ≤
        Real.log (b : ℝ) - Real.log (a : ℝ) := by
    nlinarith [hlogA, hlogB]
  have hmassBase :
      (1 / 2 : ℝ) * ((alpha - 1) * Real.log y) - 3 ≤
        logFinsetMass (oddLogWindow a b) := by
    nlinarith [hnatural, hgap, log_two_lt_one_boundary]
  dsimp [a, b, z] at hmassBase ⊢
  nlinarith [hmassBase, hwidth]

/-- The rounded lower multiplicative strip costs at most one endpoint unit
plus `delta * log y`. -/
theorem lower_power_boundary_oddWindow_mass_le
    {y delta : ℝ} (hy : 1 ≤ y) (hdelta : 0 ≤ delta) :
    logFinsetMass
        (oddLogWindow (Nat.ceil y)
          (Nat.ceil (Real.rpow y (1 + delta)) - 1)) ≤
      1 + delta * Real.log y := by
  let a := Nat.ceil y
  let z := Real.rpow y (1 + delta)
  let b := Nat.ceil z - 1
  change logFinsetMass (oddLogWindow a b) ≤
    1 + delta * Real.log y
  have hyPos : 0 < y := zero_lt_one.trans_le hy
  have hzPos : 0 < z := by
    dsimp [z]
    exact Real.rpow_pos_of_pos hyPos _
  have haNat : 1 ≤ a := by
    have haReal : y ≤ (a : ℝ) := by
      dsimp [a]
      exact Nat.le_ceil y
    exact_mod_cast hy.trans haReal
  by_cases hab : a ≤ b
  · have hbNatPos : 0 < b := lt_of_lt_of_le (by omega) hab
    have haPos : (0 : ℝ) < a := by exact_mod_cast haNat
    have hbPos : (0 : ℝ) < b := by exact_mod_cast hbNatPos
    have hlogA : Real.log y ≤ Real.log (a : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hyPos haPos (by
        dsimp [a]
        exact Nat.le_ceil y)
    have hbLt : (b : ℝ) < z := by
      have hceil : (Nat.ceil z : ℝ) < z + 1 :=
        Nat.ceil_lt_add_one hzPos.le
      have hceilPos : 1 ≤ Nat.ceil z := by
        have : (0 : ℝ) < Nat.ceil z := lt_of_lt_of_le hzPos (Nat.le_ceil z)
        exact_mod_cast this
      dsimp [b]
      push_cast [Nat.cast_sub hceilPos]
      linarith
    have hlogB : Real.log (b : ℝ) ≤ Real.log z :=
      (Real.strictMonoOn_log.monotoneOn hbPos hzPos hbLt.le)
    have hlogZ : Real.log z = (1 + delta) * Real.log y := by
      dsimp [z]
      exact Real.log_rpow hyPos _
    have hnatural :=
      logFinsetMass_oddLogWindow_le_log_ratio_add_one haNat hab
    rw [hlogZ] at hlogB
    exact hnatural.trans (by nlinarith [hlogA, hlogB])
  · have hempty : oddLogWindow a b = ∅ := by
      have hba : b < a := Nat.lt_of_not_ge hab
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      have hbds := oddLogWindow_mem.mp hn
      exact (Nat.not_le_of_gt hba) (hbds.1.trans hbds.2.1)
    rw [hempty]
    simp [logFinsetMass]
    nlinarith [mul_nonneg hdelta (Real.log_nonneg hy)]

/-- The rounded upper multiplicative strip has the same uniform cost. -/
theorem upper_power_boundary_oddWindow_mass_le
    {y alpha delta : ℝ} (hy : 1 ≤ y) (hdelta : 0 ≤ delta) :
    logFinsetMass
        (oddLogWindow
          (Nat.floor (Real.rpow y (alpha - delta)) + 1)
          (Nat.floor (Real.rpow y alpha))) ≤
      1 + delta * Real.log y := by
  let u := Real.rpow y (alpha - delta)
  let v := Real.rpow y alpha
  let a := Nat.floor u + 1
  let b := Nat.floor v
  change logFinsetMass (oddLogWindow a b) ≤
    1 + delta * Real.log y
  have hyPos : 0 < y := zero_lt_one.trans_le hy
  have huPos : 0 < u := by
    dsimp [u]
    exact Real.rpow_pos_of_pos hyPos _
  have hvPos : 0 < v := by
    dsimp [v]
    exact Real.rpow_pos_of_pos hyPos _
  by_cases hab : a ≤ b
  · have haNat : 1 ≤ a := by dsimp [a]; omega
    have hbNatPos : 0 < b := lt_of_lt_of_le (by omega) hab
    have haPos : (0 : ℝ) < a := by exact_mod_cast haNat
    have hbPos : (0 : ℝ) < b := by exact_mod_cast hbNatPos
    have huLt : u < (a : ℝ) := by
      dsimp [a]
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one u
    have hbLe : (b : ℝ) ≤ v := by
      dsimp [b]
      exact Nat.floor_le (Real.rpow_nonneg hyPos.le _)
    have hlogA : Real.log u ≤ Real.log (a : ℝ) :=
      Real.strictMonoOn_log.monotoneOn huPos haPos huLt.le
    have hlogB : Real.log (b : ℝ) ≤ Real.log v :=
      Real.strictMonoOn_log.monotoneOn hbPos hvPos hbLe
    have hlogU : Real.log u = (alpha - delta) * Real.log y := by
      dsimp [u]
      exact Real.log_rpow hyPos _
    have hlogV : Real.log v = alpha * Real.log y := by
      dsimp [v]
      exact Real.log_rpow hyPos _
    have hnatural :=
      logFinsetMass_oddLogWindow_le_log_ratio_add_one haNat hab
    rw [hlogU] at hlogA
    rw [hlogV] at hlogB
    exact hnatural.trans (by nlinarith [hlogA, hlogB])
  · have hempty : oddLogWindow a b = ∅ := by
      have hba : b < a := Nat.lt_of_not_ge hab
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      have hbds := oddLogWindow_mem.mp hn
      exact (Nat.not_le_of_gt hba) (hbds.1.trans hbds.2.1)
    rw [hempty]
    simp [logFinsetMass]
    nlinarith [mul_nonneg hdelta (Real.log_nonneg hy)]

end

end Tao
end Erdos1135
