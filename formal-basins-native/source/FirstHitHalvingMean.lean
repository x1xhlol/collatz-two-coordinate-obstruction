import FirstHitHalving
import LogarithmicParity
import OddFullMean
import ActualClockAdapter

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.Halving

namespace CollatzCylinderPacking.Arithmetic

theorem firstHit_halving_cumulative_defect (N : ℕ) (t : ℝ) :
    0 ≤ logarithmicCumulative (fun q => firstHitWeight N (2 * q)) t -
      logarithmicCumulative (firstHitWeight N) t ∧
    logarithmicCumulative (fun q => firstHitWeight N (2 * q)) t -
      logarithmicCumulative (firstHitWeight N) t ≤ 1 := by
  classical
  let S := Finset.range ⌊Real.exp t⌋₊
  let j := N / 2 - 1
  have he : logarithmicCumulative (fun q => firstHitWeight N (2 * q)) t -
      logarithmicCumulative (firstHitWeight N) t =
      ∑ n ∈ S, (firstHitWeight N (2 * (n + 1)) - firstHitWeight N (n + 1)) / (n + 1 : ℕ) := by
    unfold logarithmicCumulative
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hterm (n : ℕ) :
      0 ≤ (firstHitWeight N (2 * (n + 1)) - firstHitWeight N (n + 1)) / (n + 1 : ℕ) ∧
      (firstHitWeight N (2 * (n + 1)) - firstHitWeight N (n + 1)) / (n + 1 : ℕ) ≤
        if n = j then (1 : ℝ) else 0 := by
    have hd := firstHitWeight_halving_defect N (n + 1)
    refine ⟨div_nonneg hd.1 (by positivity), ?_⟩
    by_cases htarget : 2 * (n + 1) = N
    · have hn : n = j := by dsimp [j]; omega
      rw [if_pos hn]
      apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
      have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact hd.2.trans hn1
    · rw [firstHitWeight_halving htarget, sub_self, zero_div]
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

theorem firstHit_odd_full_cumulative_recurrence (N : ℕ) (t : ℝ) :
    |logarithmicCumulative (firstHitWeight N) (t + Real.log 2) -
      logarithmicCumulative (oddFirstHitWeight N) (t + Real.log 2) -
      (1 / 2 : ℝ) * logarithmicCumulative (firstHitWeight N) t| ≤ 1 / 2 := by
  have h := logarithmic_cumulative_parity (firstHitWeight N) (t + Real.log 2)
  have ho : oddRestriction (firstHitWeight N) = oddFirstHitWeight N := rfl
  rw [ho, add_sub_cancel_right] at h
  have hb := firstHit_halving_cumulative_defect N t
  rw [h]
  have he : logarithmicCumulative (oddFirstHitWeight N) (t + Real.log 2) +
      (1 / 2 : ℝ) * logarithmicCumulative (fun q => firstHitWeight N (2 * q)) t -
      logarithmicCumulative (oddFirstHitWeight N) (t + Real.log 2) -
      (1 / 2 : ℝ) * logarithmicCumulative (firstHitWeight N) t =
      (1 / 2 : ℝ) * (logarithmicCumulative (fun q => firstHitWeight N (2 * q)) t -
        logarithmicCumulative (firstHitWeight N) t) := by ring
  rw [he, abs_of_nonneg (mul_nonneg (by norm_num) hb.1)]
  linarith

/-- The actual full first-hit weight has twice the odd logarithmic mean.
The exceptional initial hit at an even target is absorbed by a proved
uniformly bounded harmonic correction. -/
theorem firstHit_full_mean_of_odd_mean (N : ℕ) {D : ℝ}
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 D)) :
    Tendsto (fun t : ℝ => logarithmicCumulative (firstHitWeight N) t / t)
      atTop (𝓝 (2 * D)) := by
  apply CollatzCanonical.OddFullMean.mean_tendsto_twice_of_half_shift
    (logarithmicCumulative (firstHitWeight N))
    (logarithmicCumulative (oddFirstHitWeight N)) (Real.log 2) 2 (1 / 2) D
    (Real.log_nonneg (by norm_num)) (by norm_num) (by norm_num) _ _ hodd
  · intro t ht
    have ht0 : 0 < t := by linarith
    have hb := logarithmicCumulative_linear_bound
      (fun q => (firstHitWeight_bounds N q).1) (fun q => (firstHitWeight_bounds N q).2) ht0.le
    rw [abs_div, abs_of_pos ht0]
    apply (div_le_iff₀ ht0).mpr
    linarith
  · intro t _
    exact firstHit_odd_full_cumulative_recurrence N t

end CollatzCylinderPacking.Arithmetic
