/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.UniformLift

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem syracFineScaleOscillation_eq_sum_abs_sub_uniformLift
    {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m n =
      ∑ y : ZMod (3 ^ n),
        |syracPMFMassVector n y -
          taoZModPowUniformLift hmn (syracPMFMassVector m) y| := by
  unfold syracFineScaleOscillation taoZModPowOscillation
  change
    (∑ y : ZMod (3 ^ n),
      |syracPMFMassVector n y -
        zmodPowFiberAverage m n (syracPMFMassVector n) y|) = _
  rw [zmodPowFiberAverage_syracPMFMassVector_eq_uniformLift hmn]

@[simp] theorem syracFineScaleOscillation_self (n : ℕ) :
    syracFineScaleOscillation n n = 0 := by
  rw [syracFineScaleOscillation_eq_sum_abs_sub_uniformLift (le_refl n)]
  rw [taoZModPowUniformLift_refl]
  simp

theorem sub_uniformLift_trans_pointwise
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (c : ZMod (3 ^ n) → ℝ)
    (d : ZMod (3 ^ s) → ℝ)
    (e : ZMod (3 ^ r) → ℝ) (y : ZMod (3 ^ n)) :
    c y - taoZModPowUniformLift (hrs.trans hsn) e y =
      (c y - taoZModPowUniformLift hsn d y) +
        taoZModPowUniformLift hsn
          (fun x => d x - taoZModPowUniformLift hrs e x) y := by
  rw [congrFun (taoZModPowUniformLift_sub hsn d
    (taoZModPowUniformLift hrs e)) y]
  rw [congrFun (taoZModPowUniformLift_trans hrs hsn e) y]
  ring

theorem sum_abs_sub_uniformLift_trans_le
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (c : ZMod (3 ^ n) → ℝ)
    (d : ZMod (3 ^ s) → ℝ)
    (e : ZMod (3 ^ r) → ℝ) :
    (∑ y : ZMod (3 ^ n),
      |c y - taoZModPowUniformLift (hrs.trans hsn) e y|) ≤
      (∑ x : ZMod (3 ^ s),
        |d x - taoZModPowUniformLift hrs e x|) +
        ∑ y : ZMod (3 ^ n),
          |c y - taoZModPowUniformLift hsn d y| := by
  calc
    (∑ y : ZMod (3 ^ n),
        |c y - taoZModPowUniformLift (hrs.trans hsn) e y|) =
      ∑ y : ZMod (3 ^ n),
        |(c y - taoZModPowUniformLift hsn d y) +
          taoZModPowUniformLift hsn
            (fun x => d x - taoZModPowUniformLift hrs e x) y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [sub_uniformLift_trans_pointwise hrs hsn c d e y]
    _ ≤ ∑ y : ZMod (3 ^ n),
        (|c y - taoZModPowUniformLift hsn d y| +
          |taoZModPowUniformLift hsn
            (fun x => d x - taoZModPowUniformLift hrs e x) y|) := by
      apply Finset.sum_le_sum
      intro y hy
      exact abs_add_le _ _
    _ = (∑ y : ZMod (3 ^ n),
          |c y - taoZModPowUniformLift hsn d y|) +
        ∑ y : ZMod (3 ^ n),
          |taoZModPowUniformLift hsn
            (fun x => d x - taoZModPowUniformLift hrs e x) y| := by
      rw [Finset.sum_add_distrib]
    _ = (∑ y : ZMod (3 ^ n),
          |c y - taoZModPowUniformLift hsn d y|) +
        ∑ x : ZMod (3 ^ s),
          |d x - taoZModPowUniformLift hrs e x| := by
      rw [taoZModPowUniformLift_sum_abs]
    _ = (∑ x : ZMod (3 ^ s),
          |d x - taoZModPowUniformLift hrs e x|) +
        ∑ y : ZMod (3 ^ n),
          |c y - taoZModPowUniformLift hsn d y| := by
      rw [add_comm]

theorem syracFineScaleOscillation_le_add
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) :
    syracFineScaleOscillation r n ≤
      syracFineScaleOscillation r s +
        syracFineScaleOscillation s n := by
  rw [syracFineScaleOscillation_eq_sum_abs_sub_uniformLift
      (hrs.trans hsn),
    syracFineScaleOscillation_eq_sum_abs_sub_uniformLift hrs,
    syracFineScaleOscillation_eq_sum_abs_sub_uniformLift hsn]
  exact sum_abs_sub_uniformLift_trans_le hrs hsn
    (syracPMFMassVector n) (syracPMFMassVector s)
      (syracPMFMassVector r)

theorem syracFineScaleOscillation_succ_le_add
    {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m (n + 1) ≤
      syracFineScaleOscillation m n +
        syracFineScaleOscillation n (n + 1) :=
  syracFineScaleOscillation_le_add hmn (Nat.le_succ n)

end

end Tao

end Erdos1135Predecessor
