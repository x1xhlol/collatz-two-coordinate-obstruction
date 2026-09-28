import BasinIndicatorTransport
import LogarithmicParity
import OddFullMean
import ActualClockAdapter

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.Halving

namespace CollatzCylinderPacking.Arithmetic

noncomputable def oddBasinIndicator (N q : ℕ) : ℝ :=
  if q % 2 = 1 then basinIndicator N q else 0

theorem basin_halving_cumulative_defect (N : ℕ) (t : ℝ) :
    0 ≤ logarithmicCumulative (fun q => basinIndicator N (2 * q)) t -
      logarithmicCumulative (basinIndicator N) t ∧
    logarithmicCumulative (fun q => basinIndicator N (2 * q)) t -
      logarithmicCumulative (basinIndicator N) t ≤ 1 := by
  classical
  let S := Finset.range ⌊Real.exp t⌋₊
  let j := N / 2 - 1
  have he : logarithmicCumulative (fun q => basinIndicator N (2 * q)) t -
      logarithmicCumulative (basinIndicator N) t =
      ∑ n ∈ S, (basinIndicator N (2 * (n + 1)) - basinIndicator N (n + 1)) / (n + 1 : ℕ) := by
    unfold logarithmicCumulative
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hterm (n : ℕ) :
      0 ≤ (basinIndicator N (2 * (n + 1)) - basinIndicator N (n + 1)) / (n + 1 : ℕ) ∧
      (basinIndicator N (2 * (n + 1)) - basinIndicator N (n + 1)) / (n + 1 : ℕ) ≤
        if n = j then (1 : ℝ) else 0 := by
    have hd := basinIndicator_halving_defect N (n + 1)
    refine ⟨div_nonneg hd.1 (by positivity), ?_⟩
    by_cases htarget : 2 * (n + 1) = N
    · have hn : n = j := by dsimp [j]; omega
      rw [if_pos hn]
      apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
      have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact hd.2.trans hn1
    · rw [basinIndicator_halving htarget, sub_self, zero_div]
      split_ifs <;> norm_num
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun n _ => (hterm n).1)
  · calc
      _ ≤ ∑ n ∈ S, if n = j then (1 : ℝ) else 0 :=
        Finset.sum_le_sum (fun n _ => (hterm n).2)
      _ ≤ 1 := by
        simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num

theorem basin_odd_full_cumulative_recurrence (N : ℕ) (t : ℝ) :
    |logarithmicCumulative (basinIndicator N) (t + Real.log 2) -
      logarithmicCumulative (oddBasinIndicator N) (t + Real.log 2) -
      (1 / 2 : ℝ) * logarithmicCumulative (basinIndicator N) t| ≤ 1 / 2 := by
  have h := logarithmic_cumulative_parity (basinIndicator N) (t + Real.log 2)
  have ho : oddRestriction (basinIndicator N) = oddBasinIndicator N := rfl
  rw [ho, add_sub_cancel_right] at h
  have hb := basin_halving_cumulative_defect N t
  rw [h]
  have he : logarithmicCumulative (oddBasinIndicator N) (t + Real.log 2) +
      (1 / 2 : ℝ) * logarithmicCumulative (fun q => basinIndicator N (2 * q)) t -
      logarithmicCumulative (oddBasinIndicator N) (t + Real.log 2) -
      (1 / 2 : ℝ) * logarithmicCumulative (basinIndicator N) t =
      (1 / 2 : ℝ) * (logarithmicCumulative (fun q => basinIndicator N (2 * q)) t -
        logarithmicCumulative (basinIndicator N) t) := by ring
  rw [he, abs_of_nonneg (mul_nonneg (by norm_num) hb.1)]
  linarith

/-- The actual basin indicator has twice the odd logarithmic mean.
The exceptional initial hit at an even target is absorbed by a proved
uniformly bounded harmonic correction. -/
theorem basin_full_mean_of_odd_mean (N : ℕ) {D : ℝ}
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddBasinIndicator N) t / t)
      atTop (𝓝 D)) :
    Tendsto (fun t : ℝ => logarithmicCumulative (basinIndicator N) t / t)
      atTop (𝓝 (2 * D)) := by
  apply CollatzCanonical.OddFullMean.mean_tendsto_twice_of_half_shift
    (logarithmicCumulative (basinIndicator N))
    (logarithmicCumulative (oddBasinIndicator N)) (Real.log 2) 2 (1 / 2) D
    (Real.log_nonneg (by norm_num)) (by norm_num) (by norm_num) _ _ hodd
  · intro t ht
    have ht0 : 0 < t := by linarith
    have hb := logarithmicCumulative_linear_bound
      (fun q => (basinIndicator_bounds N q).1) (fun q => (basinIndicator_bounds N q).2) ht0.le
    rw [abs_div, abs_of_pos ht0]
    apply (div_le_iff₀ ht0).mpr
    linarith
  · intro t _
    exact basin_odd_full_cumulative_recurrence N t

end CollatzCylinderPacking.Arithmetic
