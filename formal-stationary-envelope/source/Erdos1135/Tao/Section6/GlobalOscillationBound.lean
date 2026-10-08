import Erdos1135.Tao.Fourier.OscillationAlgebra

/-!
# Global Syracuse Oscillation Bound

This leaf bounds the complete Syracuse oscillation directly by twice its unit
mass.  It does not telescope this fallback or perform small-scale absorption.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
namespace Tao

noncomputable section

/-- Syracuse fine-scale oscillation is at most two, uniformly in both scales
whenever the lower scale projects from the upper scale. -/
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

/-- Diagonal-scale canary. -/
theorem syracFineScaleOscillation_self_le_two (n : ℕ) :
    syracFineScaleOscillation n n ≤ 2 :=
  syracFineScaleOscillation_le_two (le_refl n)

/-- Singleton-modulus boundary canary. -/
theorem syracFineScaleOscillation_zero_zero_le_two :
    syracFineScaleOscillation 0 0 ≤ 2 :=
  syracFineScaleOscillation_le_two (le_refl 0)

/-- First nontrivial cross-scale canary. -/
theorem syracFineScaleOscillation_one_two_le_two :
    syracFineScaleOscillation 1 2 ≤ 2 :=
  syracFineScaleOscillation_le_two (by omega)

end

end Tao
end Erdos1135
