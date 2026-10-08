import BasinTracePositivity
import Erdos1135Predecessor.StoppingTime
import Erdos1135Predecessor.Terras.Density.NaturalDensity

set_option autoImplicit false
open scoped BigOperators

namespace CollatzBasinMapBridges
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem rawStep_eq_predecessor_native (q : ℕ) : rawStep q = Erdos1135Predecessor.collatzStep q := by
  simp only [rawStep, Erdos1135Predecessor.collatzStep,
    CollatzConjecturePredecessor.collatzStep, Nat.even_iff]

theorem rawIterate_eq_predecessor_native (k q : ℕ) :
    rawIterate k q = (Erdos1135Predecessor.collatzStep^[k]) q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [rawIterate, ih, rawStep_eq_predecessor_native, Function.iterate_succ_apply]

theorem native_predecessor_double_basin {q N : ℕ} (h : Erdos1135Predecessor.Reaches q (2 * N)) :
    basinIndicator N q = 1 := by
  obtain ⟨k, hk⟩ := h
  have hh : rawIterate k q = 2 * N := by rw [rawIterate_eq_predecessor_native]; exact hk
  have hhit := raw_hit_double_implies_shortcut_hit k q N hh
  simp only [basinIndicator, if_pos hhit]

theorem native_positive_count_as_sum (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hzero : 0 ∉ S) (X : ℕ) :
    (Erdos1135Predecessor.Terras.natCount S (X + 1) : ℝ) =
      ∑ n ∈ Finset.range X, if n + 1 ∈ S then (1 : ℝ) else 0 := by
  classical
  unfold Erdos1135Predecessor.Terras.natCount
  induction X with
  | zero => simp [Nat.count_succ, hzero]
  | succ X ih =>
    rw [Nat.count_succ, Nat.cast_add, ih, Finset.sum_range_succ]
    congr 1
    split_ifs <;> norm_num

theorem native_countBelow_le_basin_prefix (S : Set ℕ) (N X : ℕ)
    (hS : ∀ q ∈ S, 0 < q ∧ basinIndicator N q = 1) :
    (Erdos1135Predecessor.Terras.natCount S X : ℝ) ≤
      ∑ n ∈ Finset.range X, basinIndicator N (n + 1) := by
  classical
  have hzero : 0 ∉ S := fun hz => (Nat.lt_irrefl 0) (hS 0 hz).1
  have hmono : Erdos1135Predecessor.Terras.natCount S X ≤
      Erdos1135Predecessor.Terras.natCount S (X + 1) := by
    unfold Erdos1135Predecessor.Terras.natCount
    exact Nat.count_monotone (fun n => n ∈ S) (Nat.le_succ X)
  calc
    _ ≤ (Erdos1135Predecessor.Terras.natCount S (X + 1) : ℝ) := Nat.cast_le.mpr hmono
    _ = _ := native_positive_count_as_sum S hzero X
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n + 1 ∈ S
      · rw [if_pos hn, (hS (n + 1) hn).2]
      · rw [if_neg hn]
        exact (basinIndicator_bounds N (n + 1)).1

#print axioms native_predecessor_double_basin
#print axioms native_countBelow_le_basin_prefix

end CollatzBasinMapBridges
