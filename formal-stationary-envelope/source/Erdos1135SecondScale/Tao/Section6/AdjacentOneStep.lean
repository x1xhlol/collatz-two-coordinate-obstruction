/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.UniformLift

/-!
# One-Step Projective Oscillation

This leaf rewrites Syracuse oscillation as an L1 distance to a normalized
lower-level lift and proves the lossless one-step triangle inequality.  The
finite adjacent telescope and all rate summation remain separate consumers.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Syracuse oscillation is the L1 distance from the ambient law to the
normalized lift of its projective lower-level marginal. -/
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

/-- Oscillation between one level and itself vanishes. -/
@[simp] theorem syracFineScaleOscillation_self (n : ℕ) :
    syracFineScaleOscillation n n = 0 := by
  rw [syracFineScaleOscillation_eq_sum_abs_sub_uniformLift (le_refl n)]
  rw [taoZModPowUniformLift_refl]
  simp

/-- Signed differences decompose exactly through one normalized intermediate
level. -/
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

/-- Exact lift isometry and pointwise triangle give the lossless projective
L1 triangle through an intermediate level. -/
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

/-- Projective Syracuse oscillations satisfy the lossless three-level
triangle inequality. -/
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

/-- One adjacent projective step.  This is the induction step for the later
finite telescope. -/
theorem syracFineScaleOscillation_succ_le_add
    {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m (n + 1) ≤
      syracFineScaleOscillation m n +
        syracFineScaleOscillation n (n + 1) :=
  syracFineScaleOscillation_le_add hmn (Nat.le_succ n)

/-- Bottom-level one-step canary. -/
theorem syracFineScaleOscillation_zero_succ_le_add (n : ℕ) :
    syracFineScaleOscillation 0 (n + 1) ≤
      syracFineScaleOscillation 0 n +
        syracFineScaleOscillation n (n + 1) :=
  syracFineScaleOscillation_succ_le_add (Nat.zero_le n)

/-- Concrete `1 ≤ 2 ≤ 3` one-step canary. -/
theorem syracFineScaleOscillation_one_three_le :
    syracFineScaleOscillation 1 3 ≤
      syracFineScaleOscillation 1 2 +
        syracFineScaleOscillation 2 3 := by
  exact syracFineScaleOscillation_succ_le_add
    (show 1 ≤ 2 by omega)

end

end Tao
end Erdos1135SecondScale
