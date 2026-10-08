/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeSourceMarginCap

/-!
# Canonical Outside-Eprime Native Budgets

This proof leaf closes the two scalar budget transformations used by the
small and large branches of the canonical outside-`E'_p` estimate.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Uniform real constant obtained after the radius-window and
floor-separation losses. -/
noncomputable def lemma79OutsideEprimeMassConstant
    (C32 c32 : ℝ) : ℝ :=
  896 * Real.exp (c32 ^ 2) * Real.exp ((c32 / 2) ^ 2) *
    ((300 * C32) *
      (lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) +
        lemma77HorizontalLinearCountConstant (c32 / 4)))

theorem lemma79OutsideEprimeMassConstant_nonneg
    {C32 c32 : ℝ} (hC32 : 0 ≤ C32) (hc32 : 0 < c32) :
    0 ≤ lemma79OutsideEprimeMassConstant C32 c32 := by
  have hGaussian :
      0 ≤ lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) :=
    lemma77HorizontalGaussianCountConstant_nonneg
      (sq_pos_of_pos (by positivity))
  have hLinear :
      0 ≤ lemma77HorizontalLinearCountConstant (c32 / 4) :=
    lemma77HorizontalLinearCountConstant_nonneg (by positivity)
  unfold lemma79OutsideEprimeMassConstant
  positivity

/-- Every PMF event has enough budget on the small branch
`sMin < 30 * X`. -/
theorem lemma79PMFEvent_outerMeasure_le_smallBranch
    {Ω : Type*} (mu : PMF Ω) (Event : Set Ω)
    {sMin X : ℝ}
    (hsMin : 1 ≤ sMin)
    (hsmall : sMin < 30 * X) :
    mu.toOuterMeasure Event ≤
      ENNReal.ofReal (30 * X / sMin) := by
  have hsMin_pos : 0 < sMin :=
    lt_of_lt_of_le (by norm_num) hsMin
  have hratio : (1 : ℝ) ≤ 30 * X / sMin :=
    (one_le_div hsMin_pos).2 hsmall.le
  calc
    mu.toOuterMeasure Event ≤ mu.toOuterMeasure Set.univ :=
      mu.toOuterMeasure.mono (Set.subset_univ Event)
    _ = 1 :=
      (mu.toOuterMeasure_apply_eq_one_iff Set.univ).2
        (Set.subset_univ _)
    _ ≤ ENNReal.ofReal (30 * X / sMin) :=
      ENNReal.one_le_ofReal.2 hratio

/-- The explicit horizontal RHS is at most a uniform constant times
`X / sMin` once the checked window and floor bounds are supplied. -/
theorem lemma79OutsideEprimeExplicitRHS_le_scale
    {C32 c32 sMin X : ℝ} {R : ℕ}
    (hC32 : 0 ≤ C32) (hc32 : 0 < c32)
    (hsMin : 0 < sMin)
    (hwindow : (((2 * R + 1 : ℕ) : ℝ)) ≤ 7 * X)
    (hfloor :
      sMin / 32 <
        (Nat.floor (sigmaSeparationScale sMin) : ℝ)) :
    ((2 * R + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal
          (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) ≤
      ENNReal.ofReal
        (lemma79OutsideEprimeMassConstant C32 c32 * X / sMin) := by
  let d : ℝ :=
    Nat.floor (sigmaSeparationScale sMin)
  let K : ℝ :=
    (300 * C32) *
      (lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) +
        lemma77HorizontalLinearCountConstant (c32 / 4))
  have hGaussian :
      0 ≤ lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) :=
    lemma77HorizontalGaussianCountConstant_nonneg
      (sq_pos_of_pos (by positivity))
  have hLinear :
      0 ≤ lemma77HorizontalLinearCountConstant (c32 / 4) :=
    lemma77HorizontalLinearCountConstant_nonneg (by positivity)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) hC32)
      (add_nonneg hGaussian hLinear)
  have hd : 0 < d :=
    lt_trans (by positivity : 0 < sMin / 32)
      (by simpa [d] using hfloor)
  have hrecip : 1 / d ≤ 32 / sMin := by
    calc
      1 / d ≤ 1 / (sMin / 32) :=
        one_div_le_one_div_of_le (by positivity)
          (by simpa [d] using hfloor.le)
      _ = 32 / sMin := by field_simp [hsMin.ne']
  have hfrac :
      2 * Real.exp ((c32 / 2) ^ 2) / d ≤
        (2 * Real.exp ((c32 / 2) ^ 2)) * (32 / sMin) := by
    calc
      2 * Real.exp ((c32 / 2) ^ 2) / d =
          (2 * Real.exp ((c32 / 2) ^ 2)) * (1 / d) := by ring
      _ ≤ (2 * Real.exp ((c32 / 2) ^ 2)) * (32 / sMin) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
  have hcenter :
      (2 * Real.exp (c32 ^ 2)) *
          ((2 * Real.exp ((c32 / 2) ^ 2) / d) * K) ≤
        (2 * Real.exp (c32 ^ 2)) *
          (((2 * Real.exp ((c32 / 2) ^ 2)) * (32 / sMin)) * K) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hfrac hK) (by positivity)
  have hcenter0 :
      0 ≤ (2 * Real.exp (c32 ^ 2)) *
        ((2 * Real.exp ((c32 / 2) ^ 2) / d) * K) := by
    positivity
  have h7X0 : 0 ≤ 7 * X :=
    (show (0 : ℝ) ≤ ((2 * R + 1 : ℕ) : ℝ) by positivity).trans
      hwindow
  have hreal :
      (((2 * R + 1 : ℕ) : ℝ)) *
          lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin ≤
        lemma79OutsideEprimeMassConstant C32 c32 * X / sMin := by
    change
      (((2 * R + 1 : ℕ) : ℝ)) *
          ((2 * Real.exp (c32 ^ 2)) *
            ((2 * Real.exp ((c32 / 2) ^ 2) / d) * K)) ≤ _
    calc
      _ ≤ (7 * X) *
          ((2 * Real.exp (c32 ^ 2)) *
            ((2 * Real.exp ((c32 / 2) ^ 2) / d) * K)) :=
        mul_le_mul_of_nonneg_right hwindow hcenter0
      _ ≤ (7 * X) *
          ((2 * Real.exp (c32 ^ 2)) *
            (((2 * Real.exp ((c32 / 2) ^ 2)) * (32 / sMin)) * K)) :=
        mul_le_mul_of_nonneg_left hcenter h7X0
      _ = lemma79OutsideEprimeMassConstant C32 c32 * X / sMin := by
        dsimp [lemma79OutsideEprimeMassConstant, K]
        field_simp [hsMin.ne']
        ring
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
