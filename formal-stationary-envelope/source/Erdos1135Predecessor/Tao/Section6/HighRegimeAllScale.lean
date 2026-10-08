/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.AdjacentTelescope
import Erdos1135Predecessor.Tao.Section6.HighRegimeMixing
import Erdos1135Predecessor.Tao.Section6.InversePowerTail

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem syracFineScaleOscillation_le_of_adjacent_inverse_power
    {A m n : ℕ} {C : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hadj : ∀ r ∈ Finset.Ico m n,
      syracFineScaleOscillation r (r + 1) ≤
        C / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) :
    syracFineScaleOscillation m n ≤ C / (m : ℝ) ^ A := by
  calc
    syracFineScaleOscillation m n ≤
        ∑ r ∈ Finset.Ico m n,
          syracFineScaleOscillation r (r + 1) :=
      syracFineScaleOscillation_le_sum_adjacent hmn
    _ ≤ ∑ r ∈ Finset.Ico m n,
        C / (((r + 1 : ℕ) : ℝ) ^ (A + 1)) := by
      exact Finset.sum_le_sum hadj
    _ = C * (∑ r ∈ Finset.Ico m n,
        1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ C * (1 / (m : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left
        (sum_Ico_one_div_succ_pow_le hA hm hmn) hC
    _ = C / (m : ℝ) ^ A := by ring

end

end Tao

end Erdos1135Predecessor
