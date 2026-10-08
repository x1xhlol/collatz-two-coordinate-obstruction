import GaoShortcutBridge
import BasinIndicatorTransport
import ActualInverseOperator

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.GaoShortcut

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem prefix_avoids_of_large (H N q : ℕ) (hq : 2 ^ H * N < q) :
    ∀ i < H, iterate i q ≠ N := by
  intro i hi hh
  have hb := start_le_scaled_endpoint i q
  rw [hh] at hb
  have hp : 2 ^ i * N ≤ 2 ^ H * N := by
    exact Nat.mul_le_mul_right N (Nat.pow_le_pow_right (by decide) hi.le)
  omega

theorem basin_eq_of_good {H N q : ℕ} (hq : 2 ^ H * N < q) (hg : good H q) :
    basinIndicator N q = basinIndicator N (q + 1) := by
  have h0 := basinIndicator_prefix (prefix_avoids_of_large H N q hq)
  have h1 := basinIndicator_prefix (prefix_avoids_of_large H N (q + 1) (by omega))
  rw [h0, h1, (good_iff H q).mp hg |>.1]

theorem basin_adjacent_difference_le_one (N q : ℕ) :
    |basinIndicator N (q + 1) - basinIndicator N q| ≤ 1 := by
  have h0 := basinIndicator_bounds N q
  have h1 := basinIndicator_bounds N (q + 1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem basin_adjacent_variation_bound (N H X : ℕ) :
    (∑ q ∈ Finset.range X, |basinIndicator N (q + 1) - basinIndicator N q|) ≤
      (2 ^ H * N + 1 : ℕ) + (X : ℝ) * (1 - goodProbability H) + (2 : ℝ) ^ H := by
  classical
  let B := 2 ^ H * N + 1
  let G := ((Finset.range X).filter (good H)).card
  have hpoint (q : ℕ) :
      |basinIndicator N (q + 1) - basinIndicator N q| ≤
        (if q < B then (1 : ℝ) else 0) + (if good H q then (0 : ℝ) else 1) := by
    by_cases hq : q < B
    · simp only [hq, if_true]
      split_ifs <;> linarith [basin_adjacent_difference_le_one N q]
    · have hlarge : 2 ^ H * N < q := by dsimp [B] at hq; omega
      simp only [hq, if_false, zero_add]
      split_ifs with hg
      · rw [← basin_eq_of_good hlarge hg, sub_self, abs_zero]
      · exact basin_adjacent_difference_le_one N q
  have hsmall : (∑ q ∈ Finset.range X, if q < B then (1 : ℝ) else 0) ≤ B := by
    have hsub : (Finset.range X).filter (fun q => q < B) ⊆ Finset.range B := by
      intro q hq
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hq).2
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_range] at hc
    simpa using (show (((Finset.range X).filter (fun q => q < B)).card : ℝ) ≤ B
      by exact_mod_cast hc)
  have hbad : (∑ q ∈ Finset.range X, if good H q then (0 : ℝ) else 1) =
      (X : ℝ) - G := by
    have he (q : ℕ) : (if good H q then (0 : ℝ) else 1) =
        1 - (if good H q then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp [G]
  have hl : (X : ℝ) * goodProbability H - (2 : ℝ) ^ H ≤ G :=
    good_count_lower H X
  calc
    _ ≤ ∑ q ∈ Finset.range X,
        ((if q < B then (1 : ℝ) else 0) + (if good H q then (0 : ℝ) else 1)) := by
      exact Finset.sum_le_sum (fun q _ => hpoint q)
    _ = (∑ q ∈ Finset.range X, if q < B then (1 : ℝ) else 0) + ((X : ℝ) - G) := by
      rw [Finset.sum_add_distrib, hbad]
    _ ≤ (B : ℝ) + ((X : ℝ) - G) := by linarith
    _ ≤ _ := by dsimp only [B]; nlinarith

theorem basin_adjacent_variation_tendsto_zero (N : ℕ) :
    Tendsto (fun X : ℕ =>
      (∑ q ∈ Finset.range X, |basinIndicator N (q + 1) - basinIndicator N q|) / (X : ℝ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H, hH⟩ := goodProbability_eventually (ε / 2) (by linarith)
  have hprob := hH H le_rfl
  let C : ℝ := (2 ^ H * N + 1 : ℕ) + (2 : ℝ) ^ H
  obtain ⟨X0, hX0⟩ := exists_nat_gt (2 * C / ε)
  refine ⟨max X0 1, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX0le : (X0 : ℝ) ≤ X := by exact_mod_cast (le_trans (le_max_left _ _) hX)
  have hC : C < (ε / 2) * X := by
    have hs : 2 * C / ε < (X : ℝ) := lt_of_lt_of_le hX0 hX0le
    have hm := (div_lt_iff₀ hε).mp hs
    nlinarith
  have hsum0 : (0 : ℝ) ≤ ∑ q ∈ Finset.range X,
      |basinIndicator N (q + 1) - basinIndicator N q| := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsum0 hXpos.le)]
  apply (div_lt_iff₀ hXpos).mpr
  have hb := basin_adjacent_variation_bound N H X
  have hmul := mul_le_mul_of_nonneg_left hprob hXpos.le
  dsimp only [C] at hC
  nlinarith

end CollatzCanonical.GaoShortcut

#print axioms CollatzCanonical.GaoShortcut.basin_eq_of_good
#print axioms CollatzCanonical.GaoShortcut.basin_adjacent_variation_bound
#print axioms CollatzCanonical.GaoShortcut.basin_adjacent_variation_tendsto_zero
