/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.GlobalTypicalEvent
import Erdos1135Predecessor.Tao.Section6.HeadGateIndex
import Erdos1135Predecessor.Tao.Section6.HeadGateLocalization

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection6PrefixCrossing
    (q : ℝ) (full : List ℕ+) (k : ℕ) : Prop :=
  k < full.length ∧
    ((taoTupleWeight (full.take k) : ℕ) : ℝ) ≤ q ∧
    q < ((taoTupleWeight (full.take (k + 1)) : ℕ) : ℝ)

theorem taoTupleWeight_take_mono
    (full : List ℕ+) {i j : ℕ} (hij : i ≤ j) :
    taoTupleWeight (full.take i) ≤ taoTupleWeight (full.take j) := by
  have h := taoTupleWeight_take_le (full.take j) i
  simpa [List.take_take, Nat.min_eq_left hij] using h

theorem taoSection6PrefixCrossing.eq
    {q : ℝ} {full : List ℕ+} {k₁ k₂ : ℕ}
    (h₁ : taoSection6PrefixCrossing q full k₁)
    (h₂ : taoSection6PrefixCrossing q full k₂) :
    k₁ = k₂ := by
  by_cases hlt : k₁ < k₂
  · have hmono :
        taoTupleWeight (full.take (k₁ + 1)) ≤
          taoTupleWeight (full.take k₂) :=
      taoTupleWeight_take_mono full (Nat.succ_le_of_lt hlt)
    have hmono_real :
        ((taoTupleWeight (full.take (k₁ + 1)) : ℕ) : ℝ) ≤
          ((taoTupleWeight (full.take k₂) : ℕ) : ℝ) := by
      exact_mod_cast hmono
    linarith [h₁.2.2, h₂.2.1]
  · by_cases hgt : k₂ < k₁
    · have hmono :
          taoTupleWeight (full.take (k₂ + 1)) ≤
            taoTupleWeight (full.take k₁) :=
        taoTupleWeight_take_mono full (Nat.succ_le_of_lt hgt)
      have hmono_real :
          ((taoTupleWeight (full.take (k₂ + 1)) : ℕ) : ℝ) ≤
            ((taoTupleWeight (full.take k₁) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      linarith [h₂.2.2, h₁.2.1]
    · omega

theorem existsUnique_taoSection6PrefixCrossing
    {q : ℝ} {full : List ℕ+}
    (hq0 : 0 ≤ q)
    (hqfull : q < ((taoTupleWeight full : ℕ) : ℝ)) :
    ∃! k : ℕ, taoSection6PrefixCrossing q full k := by
  classical
  have hfull : full ≠ [] := by
    intro hnil
    have hbad : q < 0 := by simpa [hnil, taoTupleWeight] using hqfull
    exact (not_lt_of_ge hq0) hbad
  have hlength : 0 < full.length := by
    cases full with
    | nil => exact (hfull rfl).elim
    | cons a as => simp
  let P : ℕ → Prop := fun k =>
    k < full.length ∧
      q < ((taoTupleWeight (full.take (k + 1)) : ℕ) : ℝ)
  have hex : ∃ k, P k := by
    refine ⟨full.length - 1, ?_, ?_⟩
    · exact Nat.sub_lt hlength (by omega)
    · have hlast : full.length - 1 + 1 = full.length := by omega
      simpa [P, hlast] using hqfull
  let K := Nat.find hex
  have hKspec : P K := Nat.find_spec hex
  have hKlower :
      ((taoTupleWeight (full.take K) : ℕ) : ℝ) ≤ q := by
    by_cases hK0 : K = 0
    · rw [hK0]
      simpa [taoTupleWeight] using hq0
    · by_contra hnot
      have hlt : q < ((taoTupleWeight (full.take K) : ℕ) : ℝ) :=
        lt_of_not_ge hnot
      have hpred_lt : K - 1 < K := Nat.sub_lt (Nat.pos_of_ne_zero hK0) (by omega)
      have hpred : P (K - 1) := by
        refine ⟨hpred_lt.trans hKspec.1, ?_⟩
        have hsucc : K - 1 + 1 = K := by omega
        simpa [hsucc] using hlt
      exact (Nat.find_min hex hpred_lt) hpred
  refine ⟨K, ⟨hKspec.1, hKlower, hKspec.2⟩, ?_⟩
  intro k hk
  by_cases hkK : k < K
  · exact ((Nat.find_min hex hkK) ⟨hk.1, hk.2.2⟩).elim
  · by_cases hKk : K < k
    · have hmono :
          taoTupleWeight (full.take (K + 1)) ≤
            taoTupleWeight (full.take k) :=
        taoTupleWeight_take_mono full (Nat.succ_le_of_lt hKk)
      have hmono_real :
          ((taoTupleWeight (full.take (K + 1)) : ℕ) : ℝ) ≤
            ((taoTupleWeight (full.take k) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      linarith [hKspec.2, hk.2.1]
    · omega

theorem taoSection6_one_lt_log_three_div_log_two :
    (1 : ℝ) < Real.log 3 / Real.log 2 := by
  apply (lt_div_iff₀ taoCor63_log_two_pos).2
  simpa using
    (Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3))

theorem taoSection6GlobalTypical_starQ_crossing_of_log_budget
    {CA : ℝ} {n : ℕ}
    (hCA : 17 ≤ CA) (hn : 2 ≤ n)
    (hbudget :
      ((5 / 2 : ℝ) * CA ^ 2 + CA) * Real.log (n : ℝ) ≤
        (3 / 10 : ℝ) * (n : ℝ))
    {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full) :
    0 ≤ taoCor63StarQ CA n ∧
      taoCor63StarQ CA n < ((taoTupleWeight full : ℕ) : ℝ) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog0 : 0 ≤ Real.log (n : ℝ) := hlog.le
  have hCA0 : 0 ≤ CA := by linarith
  have hcoeff : CA ^ 2 ≤ (5 / 2 : ℝ) * CA ^ 2 + CA := by
    nlinarith [sq_nonneg CA]
  have hQbudget : CA ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hcoeff hlog0
    nlinarith [hmul, hbudget]
  have hratio_lower :=
    mul_lt_mul_of_pos_left taoSection6_one_lt_log_three_div_log_two hnreal
  have hQ0 : 0 ≤ taoCor63StarQ CA n := by
    unfold taoCor63StarQ
    nlinarith
  have hx : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
  have hepsilon : 0 < (1 : ℝ) / (5 * Real.log (n : ℝ)) := by positivity
  have hyoung :=
    young_sqrt_le_epsilon
      (A := CA) (ε := (1 : ℝ) / (5 * Real.log (n : ℝ)))
      (x := (n : ℝ) * Real.log (n : ℝ)) hepsilon hx
  have hyoung' :
      CA * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (n : ℝ) / 10 +
          (5 / 2 : ℝ) * CA ^ 2 * Real.log (n : ℝ) := by
    calc
      CA * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
          (((1 : ℝ) / (5 * Real.log (n : ℝ))) / 2) *
              ((n : ℝ) * Real.log (n : ℝ)) +
            CA ^ 2 /
              (2 * ((1 : ℝ) / (5 * Real.log (n : ℝ)))) := hyoung
      _ = (n : ℝ) / 10 +
          (5 / 2 : ℝ) * CA ^ 2 * Real.log (n : ℝ) := by
        field_simp [hlog.ne']
        ring
  have herror :
      CA * (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
        Real.log (n : ℝ)) ≤ (2 / 5 : ℝ) * (n : ℝ) := by
    nlinarith [hyoung', hbudget]
  have htotal := taoCor63StarInclusiveTypical_total_lower
    (taoSection6GlobalTypical_typical hglobal) (by
      rw [taoSection6GlobalTypical_length hglobal]
      omega)
  rw [taoSection6GlobalTypical_length hglobal] at htotal
  unfold taoCor63PrefixError at htotal
  have hweight :
      (8 / 5 : ℝ) * (n : ℝ) ≤ ((taoTupleWeight full : ℕ) : ℝ) := by
    nlinarith [htotal, herror]
  have hratio_upper :=
    mul_lt_mul_of_pos_left
      taoSection6_log_three_div_log_two_lt_eight_fifths hnreal
  have hQupper : taoCor63StarQ CA n < (8 / 5 : ℝ) * (n : ℝ) := by
    have hsub : 0 ≤ CA ^ 2 * Real.log (n : ℝ) := mul_nonneg (sq_nonneg _) hlog0
    unfold taoCor63StarQ
    nlinarith
  exact ⟨hQ0, hQupper.trans_le hweight⟩

theorem taoSection6HeadGate_of_global_prefixCrossing
    {CA : ℝ} {n k : ℕ} {full : List ℕ+}
    (hglobal : taoSection6GlobalTypical CA n full)
    (hcross : taoSection6PrefixCrossing (taoCor63StarQ CA n) full k) :
    taoSection6HeadGate CA n k
      (taoTupleWeight (full.take (k + 1))) (full.take (k + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · have hkN : k < n := by
      simpa [taoSection6GlobalTypical_length hglobal] using hcross.1
    exact taoSection6GlobalTypical_take_length hglobal (Nat.succ_le_of_lt hkN)
  · exact taoSection6GlobalTypical_take_typical hglobal
  · simpa [List.take_take, Nat.min_eq_left (Nat.le_succ k)] using hcross.2.1
  · exact hcross.2.2

theorem taoSection6HeadGate_weight_lt_two_mul
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hCA : 17 ≤ CA) (hn : 1 ≤ n)
    (hlog : 4 ≤ Real.log (n : ℝ))
    (hgate : taoSection6HeadGate CA n k l head) :
    l < 2 * n := by
  have hrange := taoSection6HeadGate_starLRange_of_log_ge_four hCA hlog hgate
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hcoeff : -CA ^ 2 + 2 * CA ≤ 0 := by nlinarith
  have hremainder :
      (-CA ^ 2 + 2 * CA) * Real.log (n : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoeff hlog0
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hratio := mul_lt_mul_of_pos_left
    taoSection6_log_three_div_log_two_lt_eight_fifths hnreal
  have hlreal : (l : ℝ) < 2 * (n : ℝ) := by
    unfold taoCor63StarLRange taoCor63StarQ at hrange
    nlinarith [hrange.2, hratio, hremainder]
  exact_mod_cast hlreal

end

end Tao

end Erdos1135Predecessor
