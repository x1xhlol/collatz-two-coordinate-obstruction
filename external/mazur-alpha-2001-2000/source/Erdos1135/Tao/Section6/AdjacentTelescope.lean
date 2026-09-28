import Mathlib.Algebra.BigOperators.Intervals
import Erdos1135.Tao.Section6.AdjacentOneStep

/-!
# Finite Adjacent Oscillation Telescope

This leaf iterates the lossless one-step projective triangle over a finite
interval.  High-regime estimates and reciprocal-power summation remain in
separate consumers.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Syracuse oscillation across two levels is bounded by the sum of all
adjacent oscillations between them. -/
theorem syracFineScaleOscillation_le_sum_adjacent
    {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤
      ∑ r ∈ Finset.Ico m n,
        syracFineScaleOscillation r (r + 1) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      simp
  | succ n hmn ih =>
      calc
        syracFineScaleOscillation m (n + 1) ≤
            syracFineScaleOscillation m n +
              syracFineScaleOscillation n (n + 1) :=
          syracFineScaleOscillation_succ_le_add hmn
        _ ≤ (∑ r ∈ Finset.Ico m n,
              syracFineScaleOscillation r (r + 1)) +
              syracFineScaleOscillation n (n + 1) :=
          add_le_add ih (le_refl _)
        _ = ∑ r ∈ Finset.Ico m (n + 1),
              syracFineScaleOscillation r (r + 1) := by
          rw [Finset.sum_Ico_succ_top hmn]

/-- Empty-interval endpoint canary. -/
theorem syracFineScaleOscillation_self_le_sum_adjacent (m : ℕ) :
    syracFineScaleOscillation m m ≤
      ∑ r ∈ Finset.Ico m m,
        syracFineScaleOscillation r (r + 1) :=
  syracFineScaleOscillation_le_sum_adjacent (le_refl m)

/-- Bottom-level interval canary, in the equivalent `Finset.range` form. -/
theorem syracFineScaleOscillation_zero_le_sum_range (n : ℕ) :
    syracFineScaleOscillation 0 n ≤
      ∑ r ∈ Finset.range n,
        syracFineScaleOscillation r (r + 1) := by
  simpa only [Nat.Ico_zero_eq_range] using
    syracFineScaleOscillation_le_sum_adjacent
      (m := 0) (n := n) (Nat.zero_le n)

/-- Singleton-interval endpoint canary. -/
theorem syracFineScaleOscillation_succ_le_sum_adjacent (m : ℕ) :
    syracFineScaleOscillation m (m + 1) ≤
      ∑ r ∈ Finset.Ico m (m + 1),
        syracFineScaleOscillation r (r + 1) :=
  syracFineScaleOscillation_le_sum_adjacent (Nat.le_succ m)

end

end Tao
end Erdos1135
