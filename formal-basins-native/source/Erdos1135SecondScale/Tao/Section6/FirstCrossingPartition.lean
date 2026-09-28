/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.GlobalTypicalEvent
import Erdos1135SecondScale.Tao.Section6.HeadGateIndex
import Erdos1135SecondScale.Tao.Section6.HeadGateLocalization

/-!
# Section 6 First-Crossing Partition

This deterministic leaf extracts Tao's unique first prefix crossing from the
repaired global event.  For each fixed `CA ≥ 17`, sufficiently large globally
typical sources produce a unique pair `k<n`, `l<2n` carrying the exact local
head gate.  It contains no PMF, Fourier, conductor, or concentration input.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Prefix crossing with Tao's weak lower and strict upper endpoint polarity. -/
noncomputable def taoSection6PrefixCrossing
    (q : ℝ) (full : List ℕ+) (k : ℕ) : Prop :=
  k < full.length ∧
    ((taoTupleWeight (full.take k) : ℕ) : ℝ) ≤ q ∧
    q < ((taoTupleWeight (full.take (k + 1)) : ℕ) : ℝ)

/-- Positive valuation coordinates make prefix weight strictly increase. -/
theorem taoTupleWeight_take_lt_take_succ
    (full : List ℕ+) {k : ℕ} (hk : k < full.length) :
    taoTupleWeight (full.take k) <
      taoTupleWeight (full.take (k + 1)) := by
  have hsum := List.sum_take_succ
    (full.map fun a : ℕ+ => (a : ℕ)) k (by simpa using hk)
  have hpos : 0 < ((full[k] : ℕ+) : ℕ) := full[k].property
  have hweight :
      taoTupleWeight (full.take (k + 1)) =
        taoTupleWeight (full.take k) + ((full[k] : ℕ+) : ℕ) := by
    simpa [taoTupleWeight, ← List.map_eq_flatMap, List.map_take] using hsum
  omega

/-- Prefix weights are monotone in the prefix length. -/
theorem taoTupleWeight_take_mono
    (full : List ℕ+) {i j : ℕ} (hij : i ≤ j) :
    taoTupleWeight (full.take i) ≤ taoTupleWeight (full.take j) := by
  have h := taoTupleWeight_take_le (full.take j) i
  simpa [List.take_take, Nat.min_eq_left hij] using h

/-- Equality at the lower endpoint belongs to the later crossing, as required
by Tao's weak/strict convention. -/
theorem taoSection6PrefixCrossing_at_prefix_weight
    (full : List ℕ+) {k : ℕ} (hk : k < full.length) :
    taoSection6PrefixCrossing
      (((taoTupleWeight (full.take k) : ℕ) : ℝ)) full k := by
  refine ⟨hk, le_rfl, ?_⟩
  exact_mod_cast taoTupleWeight_take_lt_take_succ full hk

/-- `k=0` crossing canary, including a one-coordinate source. -/
theorem taoSection6PrefixCrossing_zero
    (full : List ℕ+) (hfull : full ≠ []) :
    taoSection6PrefixCrossing 0 full 0 := by
  have hlength : 0 < full.length := by
    cases full with
    | nil => exact (hfull rfl).elim
    | cons a as => simp
  simpa [taoTupleWeight] using
    taoSection6PrefixCrossing_at_prefix_weight full hlength

/-- Terminal crossing canary `k=length-1`, hence later tail length zero. -/
theorem taoSection6PrefixCrossing_terminal_at_prefix_weight
    (full : List ℕ+) (hfull : full ≠ []) :
    taoSection6PrefixCrossing
      (((taoTupleWeight (full.take (full.length - 1)) : ℕ) : ℝ))
      full (full.length - 1) := by
  have hlength : 0 < full.length := by
    cases full with
    | nil => exact (hfull rfl).elim
    | cons a as => simp
  apply taoSection6PrefixCrossing_at_prefix_weight
  omega

/-- Two crossings of the same source and threshold have the same index.  This
does not require separate endpoint hypotheses once both crossings exist. -/
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

/-- A nonnegative real threshold below total weight has one unique prefix
crossing.  The proof selects the least prefix whose successor exceeds `q`. -/
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

/-- Elementary lower bound for Tao's logarithmic slope. -/
theorem taoSection6_one_lt_log_three_div_log_two :
    (1 : ℝ) < Real.log 3 / Real.log 2 := by
  apply (lt_div_iff₀ taoCor63_log_two_pos).2
  simpa using
    (Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3))

/-- Pointwise global crossing once the logarithmic error has entered a fixed
linear budget. -/
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

/-- For fixed `CA ≥ 17`, every sufficiently large globally typical source has
its strict first crossing inside the source horizon. -/
theorem exists_taoSection6GlobalTypical_starQ_crossing
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ Ncross : ℕ, ∀ n : ℕ, Ncross ≤ n →
      ∀ full : List ℕ+, taoSection6GlobalTypical CA n full →
        0 ≤ taoCor63StarQ CA n ∧
          taoCor63StarQ CA n < ((taoTupleWeight full : ℕ) : ℝ) := by
  let D : ℝ := (5 / 2 : ℝ) * CA ^ 2 + CA
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg CA]
  obtain ⟨Nbudget, hNbudget⟩ :=
    exists_taoSection6_const_mul_log_le D (3 / 10 : ℝ) hD (by norm_num)
  refine ⟨max Nbudget 2, ?_⟩
  intro n hn full hglobal
  apply taoSection6GlobalTypical_starQ_crossing_of_log_budget hCA
  · exact (le_max_right _ _).trans hn
  · simpa [D] using hNbudget n ((le_max_left _ _).trans hn)
  · exact hglobal

/-- A global crossing restricted to its successor prefix is exactly the local
head gate, with `l` equal to total head weight. -/
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

/-- Every sufficiently large local head gate lies in the crude weight box
`l<2n`. -/
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

/-- Eventual unique bounded `(k,l)` partition datum produced by the repaired
global event. -/
theorem exists_taoSection6GlobalTypical_unique_bounded_headGate
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ full : List ℕ+, taoSection6GlobalTypical CA n full →
        ∃! kl : ℕ × ℕ,
          kl.1 < n ∧ kl.2 < 2 * n ∧
            taoSection6HeadGate CA n kl.1 kl.2
              (full.take (kl.1 + 1)) := by
  obtain ⟨Ncross, hNcross⟩ :=
    exists_taoSection6GlobalTypical_starQ_crossing CA hCA
  obtain ⟨Nlog, hNlog⟩ := taoCor63_exists_nat_log_gt 4
  refine ⟨max Ncross (max Nlog 2), ?_⟩
  intro n hn full hglobal
  have hncross : Ncross ≤ n := (le_max_left _ _).trans hn
  have hnlog : Nlog ≤ n := (le_max_left _ _).trans
    ((le_max_right Ncross (max Nlog 2)).trans hn)
  have hn2 : 2 ≤ n := (le_max_right Nlog 2).trans
    ((le_max_right Ncross (max Nlog 2)).trans hn)
  have hQ := hNcross n hncross full hglobal
  obtain ⟨k, hk, hkUnique⟩ :=
    existsUnique_taoSection6PrefixCrossing hQ.1 hQ.2
  let l := taoTupleWeight (full.take (k + 1))
  have hgate : taoSection6HeadGate CA n k l (full.take (k + 1)) := by
    simpa [l] using taoSection6HeadGate_of_global_prefixCrossing hglobal hk
  have hl : l < 2 * n :=
    taoSection6HeadGate_weight_lt_two_mul hCA (by omega)
      (le_of_lt (hNlog n hnlog)) hgate
  refine ⟨(k, l), ⟨by simpa [taoSection6GlobalTypical_length hglobal] using hk.1,
    hl, hgate⟩, ?_⟩
  rintro ⟨k', l'⟩ hkl
  have hcross' : taoSection6PrefixCrossing (taoCor63StarQ CA n) full k' := by
    have hgate' := hkl.2.2
    have hgateCross := taoSection6HeadGate_crossing hgate'
    refine ⟨by simpa [taoSection6GlobalTypical_length hglobal] using hkl.1,
      ?_, ?_⟩
    · simpa [List.take_take, Nat.min_eq_left (Nat.le_succ k')] using hgateCross.1
    · exact hgateCross.2
  have hkEq : k' = k := hkUnique k' hcross'
  subst k'
  have hlEq : l' = l := by
    have hw := taoSection6HeadGate_weight hkl.2.2
    simpa [l] using hw.symm
  subst l'
  rfl

end

end Tao
end Erdos1135SecondScale
