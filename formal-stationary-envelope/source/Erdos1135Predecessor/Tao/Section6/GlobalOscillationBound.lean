/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.OscillationAlgebra

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem syracFineScaleOscillation_le_two
    {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤ 2 := by
  have hmass :
      (∑ y : ZMod (3 ^ n), |syracPMFMassVector n y|) = 1 := by
    classical
    calc
      (∑ y : ZMod (3 ^ n), |syracPMFMassVector n y|) =
          ∑ y : ZMod (3 ^ n), (syracPMF n y).toReal := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [syracPMFMassVector,
          abs_of_nonneg ENNReal.toReal_nonneg]
      _ = 1 := pmf_sum_toReal (syracPMF n)
  calc
    syracFineScaleOscillation m n =
        taoZModPowOscillation m n (syracPMFMassVector n) := rfl
    _ ≤ 2 * ∑ y : ZMod (3 ^ n), |syracPMFMassVector n y| :=
      taoZModPowOscillation_le_two_mul_sum_abs hmn _
    _ = 2 := by rw [hmass, mul_one]

end

end Tao

end Erdos1135Predecessor
