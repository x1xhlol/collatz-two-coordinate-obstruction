/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.AdjacentOneStep
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

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

end

end Tao

end Erdos1135Predecessor
