import PadicAffineHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem padicThreeHaar_doubling_preserving :
    MeasurePreserving (fun x : ℤ_[3] => 2 * x) padicThreeHaar padicThreeHaar := by
  let T : ℤ_[3] →+ ℤ_[3] :=
    { toFun := fun x => 2 * x
      map_zero' := mul_zero _
      map_add' := fun x y => mul_add _ x y }
  apply AddMonoidHom.measurePreserving (f := T)
    (by change Continuous (fun x : ℤ_[3] => 2 * x); fun_prop) ?_ rfl
  intro y
  refine ⟨(↑(padicTwoUnit⁻¹) : ℤ_[3]) * y, ?_⟩
  change (2 : ℤ_[3]) * (↑(padicTwoUnit⁻¹) * y) = y
  rw [← padicTwoUnit_coe, ← mul_assoc, Units.mul_inv, one_mul]

theorem padicThree_doubling_measurableEmbedding :
    MeasurableEmbedding (fun x : ℤ_[3] => 2 * x) :=
  ((show Continuous (fun x : ℤ_[3] => 2 * x) by fun_prop).isClosedEmbedding
    (fun _ _ h => mul_left_cancel₀ (by norm_num : (2 : ℤ_[3]) ≠ 0) h)).measurableEmbedding

theorem padicAffineBranch_measurableEmbedding (a : ℕ+) :
    MeasurableEmbedding (padicAffineBranch a) :=
  ((padicAffineBranch_continuous a).isClosedEmbedding
    (padicAffineBranch_injective a)).measurableEmbedding

noncomputable def padicOddLift (f : ℤ_[3] → ℝ) : ℤ_[3] → ℝ :=
  Function.extend (padicAffineBranch 1) f (fun _ => 0)

theorem padicOddLift_apply_branch (f : ℤ_[3] → ℝ) (x : ℤ_[3]) :
    padicOddLift f (padicAffineBranch 1 x) = f x :=
  (padicAffineBranch_injective 1).extend_apply f (fun _ => 0) x

theorem padicOddLift_eq_zero (f : ℤ_[3] → ℝ) {x : ℤ_[3]}
    (hx : x ∉ Set.range (padicAffineBranch 1)) : padicOddLift f x = 0 :=
  Function.extend_apply' f (fun _ => 0) x hx

theorem padicOddLift_measurable {f : ℤ_[3] → ℝ} (hf : Measurable f) :
    Measurable (padicOddLift f) :=
  (padicAffineBranch_measurableEmbedding 1).measurable_extend hf measurable_const

theorem padicOddLift_indicator (f : ℤ_[3] → ℝ) :
    (Set.range (padicAffineBranch 1)).indicator (padicOddLift f) = padicOddLift f := by
  funext x
  by_cases hx : x ∈ Set.range (padicAffineBranch 1)
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx, padicOddLift_eq_zero f hx]

theorem padicOddLift_integrable_iff (f : ℤ_[3] → ℝ) :
    Integrable (padicOddLift f) padicThreeHaar ↔ Integrable f padicThreeHaar := by
  have h := (padicAffineBranch_measurableEmbedding 1).integrable_map_iff
    (μ := padicThreeHaar) (g := padicOddLift f)
  simp only [Function.comp_def, padicOddLift_apply_branch] at h
  rw [padicAffineBranch_map_haar,
    integrable_smul_measure (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by finiteness)] at h
  change IntegrableOn (padicOddLift f) (Set.range (padicAffineBranch 1)) padicThreeHaar ↔
    Integrable f padicThreeHaar at h
  rw [← integrable_indicator_iff (padicAffineBranch_range_measurable 1),
    padicOddLift_indicator] at h
  exact h

theorem padicOddLift_integral (f : ℤ_[3] → ℝ) :
    (∫ x : ℤ_[3], padicOddLift f x ∂padicThreeHaar) =
      (1 / 3 : ℝ) * ∫ x : ℤ_[3], f x ∂padicThreeHaar := by
  have h := (padicAffineBranch_measurableEmbedding 1).integral_map
    (μ := padicThreeHaar) (padicOddLift f)
  simp only [padicOddLift_apply_branch] at h
  rw [padicAffineBranch_map_haar, integral_smul_measure,
    ← integral_indicator (padicAffineBranch_range_measurable 1), padicOddLift_indicator] at h
  norm_num at h
  linarith

theorem padicOddLift_nonneg {f : ℤ_[3] → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℤ_[3]) :
    0 ≤ padicOddLift f x := by
  by_cases hx : x ∈ Set.range (padicAffineBranch 1)
  · obtain ⟨y, rfl⟩ := hx
    rw [padicOddLift_apply_branch]
    exact hf y
  · rw [padicOddLift_eq_zero f hx]

theorem padicOddLift_comp_zero (f : ℤ_[3] → ℝ) (g : ℝ → ℝ) (hg : g 0 = 0) :
    (fun x => g (padicOddLift f x)) = padicOddLift (fun x => g (f x)) := by
  funext x
  by_cases hx : x ∈ Set.range (padicAffineBranch 1)
  · obtain ⟨y, rfl⟩ := hx
    simp only [padicOddLift_apply_branch]
  · simp only [padicOddLift_eq_zero _ hx, hg]

theorem padicOddLift_sub (f g : ℤ_[3] → ℝ) :
    (fun x => padicOddLift f x - padicOddLift g x) = padicOddLift (fun x => f x - g x) := by
  funext x
  by_cases hx : x ∈ Set.range (padicAffineBranch 1)
  · obtain ⟨y, rfl⟩ := hx
    simp only [padicOddLift_apply_branch]
  · simp only [padicOddLift_eq_zero _ hx, sub_self]

#print axioms padicThreeHaar_doubling_preserving
#print axioms padicOddLift_integrable_iff
#print axioms padicOddLift_integral

end Erdos1135.Tao
