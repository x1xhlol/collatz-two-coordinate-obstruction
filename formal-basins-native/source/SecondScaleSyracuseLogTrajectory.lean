import Erdos1135SecondScale.Tao.Syracuse.FirstPassageInterval
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao

noncomputable def clockDrift : ℝ := Real.log (4 / 3 : ℝ)

noncomputable def logCorrection (q j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, Real.log (1 + 1 / (3 * ((syracuse^[i]) q : ℝ)))

theorem clockDrift_pos : 0 < clockDrift := Real.log_pos (by norm_num)

theorem clockDrift_ge_quarter : (1 / 4 : ℝ) ≤ clockDrift := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  norm_num at h
  unfold clockDrift
  linarith

theorem clockDrift_eq : clockDrift = 2 * Real.log 2 - Real.log 3 := by
  unfold clockDrift
  rw [Real.log_div (by norm_num) (by norm_num)]
  have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] at h
    exact h
  rw [h]

theorem syracuse_iterate_pos_clock {q : ℕ} (hq : 0 < q) (j : ℕ) :
    0 < (syracuse^[j]) q := by
  induction j with
  | zero => simpa using hq
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact syracuse_pos _

theorem syracuse_log_step {q : ℕ} (hq : 0 < q) :
    Real.log (syracuse q : ℝ) = Real.log (q : ℝ) + Real.log 3 -
      (syracuseExponent q : ℝ) * Real.log 2 + Real.log (1 + 1 / (3 * (q : ℝ))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < syracuse q := by exact_mod_cast syracuse_pos q
  have heq : (2 : ℝ) ^ syracuseExponent q * (syracuse q : ℝ) = 3 * q + 1 := by
    exact_mod_cast two_pow_syracuseExponent_mul_syracuse q
  have hfac : (3 : ℝ) * q + 1 = (3 * q) * (1 + 1 / (3 * q)) := by
    field_simp
  have hl := congrArg Real.log heq
  rw [Real.log_mul (by positivity) hsR.ne', Real.log_pow, hfac,
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) hqR.ne'] at hl
  linarith

theorem syracuse_log_trajectory {q : ℕ} (hq : Odd q) (j : ℕ) :
    Real.log ((syracuse^[j]) q : ℝ) = Real.log (q : ℝ) +
      (j : ℝ) * Real.log 3 -
      (taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) * Real.log 2 +
      logCorrection q j := by
  have hqpos : 0 < q := (by rcases hq with ⟨k, hk⟩; omega : 0 < q)
  induction j with
  | zero => simp [logCorrection, syracuseValuationPNatList, taoTupleWeight]
  | succ j ih =>
      rw [Function.iterate_succ_apply', syracuse_log_step (syracuse_iterate_pos_clock hqpos j), ih,
        taoTupleWeight_syracuseValuationPNatList_succ]
      simp only [logCorrection, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one,
        syracuseTerminalExponentPNat, PNat.mk_coe]
      ring

theorem logCorrection_nonneg {q : ℕ} (hq : 0 < q) (j : ℕ) :
    0 ≤ logCorrection q j := by
  apply Finset.sum_nonneg
  intro i hi
  apply Real.log_nonneg
  have hp : (0 : ℝ) < (syracuse^[i]) q := by
    exact_mod_cast syracuse_iterate_pos_clock hq i
  have hi : 0 ≤ (1 : ℝ) / (3 * ((syracuse^[i]) q : ℝ)) := by positivity
  linarith

theorem logCorrection_le_before_hit {B q j : ℕ} (hB : 0 < B)
    (hpre : ∀ i < j, B < (syracuse^[i]) q) :
    logCorrection q j ≤ (j : ℝ) / (3 * B) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hterm (i : ℕ) (hi : i ∈ Finset.range j) :
      Real.log (1 + 1 / (3 * ((syracuse^[i]) q : ℝ))) ≤ 1 / (3 * B) := by
    have hp : (B : ℝ) < (syracuse^[i]) q := by
      exact_mod_cast hpre i (Finset.mem_range.mp hi)
    have hlog := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + 1 / (3 * ((syracuse^[i]) q : ℝ)))
    have hdiv : (1 : ℝ) / (3 * ((syracuse^[i]) q : ℝ)) ≤ 1 / (3 * B) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  calc
    logCorrection q j ≤ ∑ _i ∈ Finset.range j, (1 : ℝ) / (3 * B) :=
      Finset.sum_le_sum hterm
    _ = (j : ℝ) / (3 * B) := by simp; ring

theorem syracuse_log_lower_of_typical {q j : ℕ} (hq : Odd q) {E : ℝ}
    (htyp : |(taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) - 2 * j| ≤ E) :
    Real.log (q : ℝ) - clockDrift * j - Real.log 2 * E ≤
      Real.log ((syracuse^[j]) q : ℝ) := by
  rw [syracuse_log_trajectory hq j, clockDrift_eq]
  have hdev := (abs_le.mp htyp).2
  have hc := logCorrection_nonneg ((by rcases hq with ⟨k, hk⟩; omega : 0 < q)) j
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

theorem syracuse_log_upper_before_hit {B q j : ℕ} (hB : 0 < B) (hq : Odd q) {E : ℝ}
    (htyp : |(taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) - 2 * j| ≤ E)
    (hpre : ∀ i < j, B < (syracuse^[i]) q) :
    Real.log ((syracuse^[j]) q : ℝ) ≤
      Real.log (q : ℝ) - clockDrift * j + Real.log 2 * E + (j : ℝ) / (3 * B) := by
  rw [syracuse_log_trajectory hq j, clockDrift_eq]
  have hdev := (abs_le.mp htyp).1
  have hc := logCorrection_le_before_hit hB hpre
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

end CollatzClockSecondScale

#print axioms CollatzClockSecondScale.syracuse_log_trajectory
#print axioms CollatzClockSecondScale.logCorrection_le_before_hit
#print axioms CollatzClockSecondScale.syracuse_log_lower_of_typical
#print axioms CollatzClockSecondScale.syracuse_log_upper_before_hit
