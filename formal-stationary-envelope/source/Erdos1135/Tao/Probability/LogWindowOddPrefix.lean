import Erdos1135.Tao.Probability.LogWindowPrefix

/-!
# Odd Prefix Logarithmic Window Mass

This module proves finite harmonic-prefix facts for the singleton odd-prefix
window `[1, X]`.  It deliberately stays below the Section 3 socket layer.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

theorem logCount_congr_on_Iic {s t : Set ℕ} {N : ℕ}
    (h : ∀ n : ℕ, n ≤ N → (n ∈ s ↔ n ∈ t)) :
    logCount s N = logCount t N := by
  classical
  unfold logCount
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiN : i + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hiff := h (i + 1) hiN
  by_cases hs : i + 1 ∈ s
  · have ht : i + 1 ∈ t := hiff.mp hs
    simp [hs, ht]
  · have ht : i + 1 ∉ t := by
      intro ht
      exact hs (hiff.mpr ht)
    simp [hs, ht]

theorem logMass_mono {X Y : ℕ} (hXY : X ≤ Y) :
    logMass X ≤ logMass Y := by
  unfold logMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro i hi
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hXY))
    (by
      intro i _hi _hnot
      exact logWeight_nonneg i)

theorem logCount_oddLogWindowSet_one_succ_of_odd {N : ℕ}
    (hodd : (N + 1) % 2 = 1) :
    logCount (oddLogWindowSet 1 (N + 1)) (N + 1) =
      logCount (oddLogWindowSet 1 N) N + logWeight N := by
  have hmem : N + 1 ∈ oddLogWindowSet 1 (N + 1) := by
    rw [oddLogWindowSet_mem]
    exact ⟨by omega, le_rfl, hodd⟩
  have hcongr :
      logCount (oddLogWindowSet 1 (N + 1)) N =
        logCount (oddLogWindowSet 1 N) N := by
    apply logCount_congr_on_Iic
    intro n hn
    rw [oddLogWindowSet_mem, oddLogWindowSet_mem]
    omega
  rw [logCount_succ_of_mem hmem, hcongr]

theorem logCount_oddLogWindowSet_one_succ_of_even {N : ℕ}
    (heven : (N + 1) % 2 ≠ 1) :
    logCount (oddLogWindowSet 1 (N + 1)) (N + 1) =
      logCount (oddLogWindowSet 1 N) N := by
  have hmem : N + 1 ∉ oddLogWindowSet 1 (N + 1) := by
    intro hn
    exact heven (oddLogWindowSet_mem.mp hn).2.2
  have hcongr :
      logCount (oddLogWindowSet 1 (N + 1)) N =
        logCount (oddLogWindowSet 1 N) N := by
    apply logCount_congr_on_Iic
    intro n hn
    rw [oddLogWindowSet_mem, oddLogWindowSet_mem]
    omega
  rw [logCount_succ_of_not_mem hmem, hcongr]

theorem logWeight_succ_odd_le (m : ℕ) :
    logWeight (2 * m + 1) ≤ logWeight (2 * m) := by
  unfold logWeight
  exact one_div_le_one_div_of_le (by positivity) (by norm_num)

theorem logCount_oddLogWindowSet_one_even_ge_half_logMass (m : ℕ) :
    (1 / 2 : ℝ) * logMass (2 * m) ≤
      logCount (oddLogWindowSet 1 (2 * m)) (2 * m) := by
  induction m with
  | zero =>
      simp [logMass, logCount]
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      have hodd_mod : (2 * m + 1) % 2 = 1 := by omega
      have heven_mod : (2 * m + 1 + 1) % 2 ≠ 1 := by omega
      have hodd_count :=
        logCount_oddLogWindowSet_one_succ_of_odd (N := 2 * m) hodd_mod
      have heven_count :=
        logCount_oddLogWindowSet_one_succ_of_even (N := 2 * m + 1) heven_mod
      have hmass_odd := logMass_succ (2 * m)
      have hmass_even := logMass_succ (2 * m + 1)
      have hw := logWeight_succ_odd_le m
      nlinarith

theorem logCount_oddLogWindowSet_one_odd_ge_half_logMass (m : ℕ) :
    (1 / 2 : ℝ) * logMass (2 * m + 1) ≤
      logCount (oddLogWindowSet 1 (2 * m + 1)) (2 * m + 1) := by
  have hodd_mod : (2 * m + 1) % 2 = 1 := by omega
  have hcount :=
    logCount_oddLogWindowSet_one_succ_of_odd (N := 2 * m) hodd_mod
  have hmass := logMass_succ (2 * m)
  have heven := logCount_oddLogWindowSet_one_even_ge_half_logMass m
  have hw_nonneg : 0 ≤ logWeight (2 * m) := logWeight_nonneg (2 * m)
  nlinarith

theorem logCount_oddLogWindowSet_one_X_ge_half_logMass (X : ℕ) :
    (1 / 2 : ℝ) * logMass X ≤ logCount (oddLogWindowSet 1 X) X := by
  rcases Nat.even_or_odd X with hX | hX
  · rcases hX with ⟨m, rfl⟩
    simpa [two_mul] using logCount_oddLogWindowSet_one_even_ge_half_logMass m
  · rcases hX with ⟨m, rfl⟩
    simpa [two_mul] using logCount_oddLogWindowSet_one_odd_ge_half_logMass m

theorem logFinsetMass_oddLogWindow_one_X_pos {X : ℕ} (hX : 1 ≤ X) :
    0 < logFinsetMass (oddLogWindow 1 X) := by
  exact logFinsetMass_pos_of_mem_pos
    (S := oddLogWindow 1 X) (n := 1)
    ((oddLogWindow_mem).mpr ⟨le_rfl, hX, by norm_num⟩)
    zero_lt_one

end Tao
end Erdos1135
