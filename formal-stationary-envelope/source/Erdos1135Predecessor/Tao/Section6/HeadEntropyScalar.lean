/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.HeadGate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos1135Predecessor.Tao

noncomputable section

def taoSection6HeadEntropyExponent (CA : ℝ) : ℕ :=
  ⌈CA ^ 2 * Real.log 2⌉₊

def taoSection6HeadEntropyFactor (n l : ℕ) : ℝ :=
  ((3 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ l

private theorem one_div_two_pow_eq_exp_neg_log (l : ℕ) :
    (1 / 2 : ℝ) ^ l = Real.exp (-(l : ℝ) * Real.log 2) := by
  calc
    (1 / 2 : ℝ) ^ l = (1 / 2 : ℝ) ^ (l : ℝ) := by
      exact (Real.rpow_natCast (1 / 2 : ℝ) l).symm
    _ = Real.exp (Real.log (1 / 2 : ℝ) * (l : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ = Real.exp (-(l : ℝ) * Real.log 2) := by
      congr 1
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [Real.log_one, zero_sub]
      ring

theorem taoSection6HeadEntropyFactor_lt_exp
    {CA : ℝ} {n l : ℕ}
    (hl : taoCor63StarQ CA n < (l : ℝ)) :
    taoSection6HeadEntropyFactor n l <
      Real.exp (CA ^ 2 * Real.log (n : ℝ) * Real.log 2) := by
  have hlog_two_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt taoCor63_log_two_pos
  have hmul := mul_lt_mul_of_pos_right hl taoCor63_log_two_pos
  have hQ :
      taoCor63StarQ CA n * Real.log 2 =
        (n : ℝ) * Real.log 3 - CA ^ 2 * Real.log (n : ℝ) * Real.log 2 := by
    rw [taoCor63StarQ]
    field_simp [hlog_two_ne]
  have hexponent :
      (n : ℝ) * Real.log 3 - (l : ℝ) * Real.log 2 <
        CA ^ 2 * Real.log (n : ℝ) * Real.log 2 := by
    rw [hQ] at hmul
    linarith
  rw [taoSection6HeadEntropyFactor]
  rw [show ((3 ^ n : ℕ) : ℝ) = (3 : ℝ) ^ n by norm_num]
  rw [taoCor63_three_pow_eq_exp_log, one_div_two_pow_eq_exp_neg_log]
  rw [← Real.exp_add]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem taoSection6HeadEntropyFactor_lt_pow
    {CA : ℝ} {n l : ℕ}
    (hn : 1 ≤ n)
    (hl : taoCor63StarQ CA n < (l : ℝ)) :
    taoSection6HeadEntropyFactor n l <
      (n : ℝ) ^ taoSection6HeadEntropyExponent CA := by
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn_one
  have hceil :
      CA ^ 2 * Real.log 2 ≤ (taoSection6HeadEntropyExponent CA : ℝ) := by
    exact Nat.le_ceil _
  have hrpow :
      Real.rpow (n : ℝ) (CA ^ 2 * Real.log 2) ≤
        Real.rpow (n : ℝ) (taoSection6HeadEntropyExponent CA : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn_one hceil
  have hexp :
      Real.exp (CA ^ 2 * Real.log (n : ℝ) * Real.log 2) ≤
        (n : ℝ) ^ taoSection6HeadEntropyExponent CA := by
    calc
      Real.exp (CA ^ 2 * Real.log (n : ℝ) * Real.log 2) =
          Real.rpow (n : ℝ) (CA ^ 2 * Real.log 2) := by
        symm
        calc
          Real.rpow (n : ℝ) (CA ^ 2 * Real.log 2) =
              Real.exp (Real.log (n : ℝ) * (CA ^ 2 * Real.log 2)) :=
            Real.rpow_def_of_pos hn_pos _
          _ = Real.exp (CA ^ 2 * Real.log (n : ℝ) * Real.log 2) := by
            congr 1
            ring
      _ ≤ Real.rpow (n : ℝ) (taoSection6HeadEntropyExponent CA : ℝ) := hrpow
      _ = (n : ℝ) ^ taoSection6HeadEntropyExponent CA :=
        Real.rpow_natCast (n : ℝ) (taoSection6HeadEntropyExponent CA)
  exact (taoSection6HeadEntropyFactor_lt_exp hl).trans_le hexp

theorem taoSection6HeadGate_entropyFactor_lt_pow
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hn : 1 ≤ n)
    (hhead : taoSection6HeadGate CA n k l head) :
    taoSection6HeadEntropyFactor n l <
      (n : ℝ) ^ taoSection6HeadEntropyExponent CA := by
  apply taoSection6HeadEntropyFactor_lt_pow hn
  simpa [taoSection6HeadGate_weight hhead] using
    (taoSection6HeadGate_crossing hhead).2

end

end Erdos1135Predecessor.Tao
