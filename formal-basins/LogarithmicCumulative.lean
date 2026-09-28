import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

noncomputable def logarithmicCumulative (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌊Real.exp t⌋₊, w (n + 1) / (n + 1 : ℕ)

theorem logarithmicCumulative_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (t : ℝ) :
    0 ≤ logarithmicCumulative w t := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (hw _) (by positivity)

theorem logarithmicCumulative_monotone {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) :
    Monotone (logarithmicCumulative w) := by
  intro s t hst
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.floor_mono (Real.exp_le_exp.mpr hst))
  · intro n _ _
    exact div_nonneg (hw _) (by positivity)

theorem logarithmicCumulative_measurable {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) :
    Measurable (logarithmicCumulative w) :=
  (logarithmicCumulative_monotone hw).measurable

theorem finite_harmonic_bound {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1 : ℕ)) ≤ 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hn1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn hn1)
    rw [Real.log_div hn.ne' hn1.ne'] at hlog
    have hrec : (1 : ℝ) / ((N : ℝ) + 1) ≤
        Real.log ((N : ℝ) + 1) - Real.log N := by
      have heq : (N : ℝ) / ((N : ℝ) + 1) - 1 = -1 / ((N : ℝ) + 1) := by
        field_simp
        ring
      rw [heq] at hlog
      rw [neg_div] at hlog
      linarith
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

theorem logarithmicCumulative_linear_bound {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    |logarithmicCumulative w t| ≤ t + 1 := by
  rw [abs_of_nonneg (logarithmicCumulative_nonneg hw0 _)]
  have hexp : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hN : 1 ≤ ⌊Real.exp t⌋₊ := (Nat.one_le_floor_iff _).mpr hexp
  calc
    logarithmicCumulative w t ≤
        ∑ n ∈ Finset.range ⌊Real.exp t⌋₊, (1 : ℝ) / (n + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro n _
      exact div_le_div_of_nonneg_right (hw1 _) (by positivity)
    _ ≤ 1 + Real.log (⌊Real.exp t⌋₊ : ℝ) := finite_harmonic_bound hN
    _ ≤ 1 + t := by
      have hpos : (0 : ℝ) < ⌊Real.exp t⌋₊ := by exact_mod_cast hN
      have hlog := Real.log_le_log hpos (Nat.floor_le (Real.exp_pos t).le)
      rw [Real.log_exp] at hlog
      linarith
    _ = t + 1 := add_comm _ _

theorem logarithmicCumulative_eq_tsum (w : ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative w t =
      ∑' n : ℕ, if Real.log (n + 1 : ℕ) ≤ t then w (n + 1) / (n + 1 : ℕ) else 0 := by
  have hmem (n : ℕ) : n ∈ Finset.range ⌊Real.exp t⌋₊ ↔ Real.log (n + 1 : ℕ) ≤ t := by
    rw [Finset.mem_range, Nat.lt_iff_add_one_le, Nat.le_floor_iff (Real.exp_pos t).le,
      Real.log_le_iff_le_exp (by positivity)]
  rw [tsum_eq_sum (s := Finset.range ⌊Real.exp t⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos ((hmem n).mp hn)]
  · intro n hn
    exact if_neg (mt (hmem n).mpr hn)

theorem logarithmicCumulative_zero (w : ℕ → ℝ) :
    logarithmicCumulative w 0 = w 1 := by
  simp [logarithmicCumulative]

#print axioms logarithmicCumulative_nonneg
#print axioms logarithmicCumulative_monotone
#print axioms logarithmicCumulative_measurable
#print axioms finite_harmonic_bound
#print axioms logarithmicCumulative_linear_bound
#print axioms logarithmicCumulative_eq_tsum
#print axioms logarithmicCumulative_zero

end CollatzCanonical.DirichletAbelian
