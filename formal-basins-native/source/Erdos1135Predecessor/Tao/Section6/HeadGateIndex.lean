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

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection6_log_three_div_log_two_lt_eight_fifths :
    Real.log 3 / Real.log 2 < (8 / 5 : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (3 : ℝ) ^ 5 < (2 : ℝ) ^ 8 := by norm_num
  have hlogpow : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) :=
    Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hlog : Real.log (3 : ℝ) < (8 / 5 : ℝ) * Real.log (2 : ℝ) := by
    calc
      Real.log (3 : ℝ) = (5 * Real.log (3 : ℝ)) / 5 := by ring
      _ < (8 * Real.log (2 : ℝ)) / 5 :=
        div_lt_div_of_pos_right hlogpow (by norm_num)
      _ = (8 / 5 : ℝ) * Real.log (2 : ℝ) := by ring
  exact (div_lt_iff₀ hlog2).2 hlog

theorem taoSection6HeadGate_index_le_of_log_budget
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hlog : 0 < Real.log (n : ℝ))
    (hbudget :
      ((3 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) ≤
        (3 / 200 : ℝ) * (n : ℝ))
    (hgate : taoSection6HeadGate CA n k l head) :
    20 * k ≤ 17 * n := by
  by_cases hk0 : k = 0
  · omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hlength := taoSection6HeadGate_length hgate
  have htyp := taoSection6HeadGate_typical hgate
  have hcross := (taoSection6HeadGate_crossing hgate).1
  have hprefix :=
    taoCor63StarInclusiveTypical_prefix_lower
      htyp hkpos (by omega : k ≤ head.length)
  rw [taoSection6IntervalWeight_zero_eq_tupleWeight_take] at hprefix
  unfold taoCor63PrefixError at hprefix
  unfold taoCor63StarQ at hcross
  have hmain :
      2 * (k : ℝ) -
          CA * (Real.sqrt ((k : ℝ) * Real.log (n : ℝ)) +
            Real.log (n : ℝ)) ≤
        (n : ℝ) * (Real.log 3 / Real.log 2) -
          CA ^ 2 * Real.log (n : ℝ) :=
    hprefix.trans hcross
  have hx : 0 ≤ (k : ℝ) * Real.log (n : ℝ) := by positivity
  have hepsilon : 0 < (1 : ℝ) / (5 * Real.log (n : ℝ)) := by positivity
  have hyoung :=
    young_sqrt_le_epsilon
      (A := CA) (ε := (1 : ℝ) / (5 * Real.log (n : ℝ)))
      (x := (k : ℝ) * Real.log (n : ℝ)) hepsilon hx
  have hyoung' :
      CA * Real.sqrt ((k : ℝ) * Real.log (n : ℝ)) ≤
        (k : ℝ) / 10 +
          (5 / 2 : ℝ) * CA ^ 2 * Real.log (n : ℝ) := by
    calc
      CA * Real.sqrt ((k : ℝ) * Real.log (n : ℝ)) ≤
          (((1 : ℝ) / (5 * Real.log (n : ℝ))) / 2) *
              ((k : ℝ) * Real.log (n : ℝ)) +
            CA ^ 2 /
              (2 * ((1 : ℝ) / (5 * Real.log (n : ℝ)))) := hyoung
      _ = (k : ℝ) / 10 +
          (5 / 2 : ℝ) * CA ^ 2 * Real.log (n : ℝ) := by
        field_simp [hlog.ne']
        ring
  have hlinear :
      (19 / 10 : ℝ) * (k : ℝ) ≤
        (n : ℝ) * (Real.log 3 / Real.log 2) +
          ((3 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) := by
    nlinarith [hmain, hyoung']
  have hnpos : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [this] at hlog
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hratio :=
    mul_lt_mul_of_pos_left
      taoSection6_log_three_div_log_two_lt_eight_fifths hnreal
  have hupper :
      (n : ℝ) * (Real.log 3 / Real.log 2) +
          ((3 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) <
        (323 / 200 : ℝ) * (n : ℝ) := by
    nlinarith [hratio, hbudget]
  have hstrict : (20 : ℝ) * (k : ℝ) < 17 * (n : ℝ) := by
    nlinarith [hlinear.trans_lt hupper]
  exact_mod_cast hstrict.le

theorem taoSection6HeadIndex_le_m_of_bounds
    {n k m : ℕ} (hn : 1 ≤ n)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    k + 1 ≤ m := by
  omega

end

end Tao

end Erdos1135Predecessor
