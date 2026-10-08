import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace Erdos1135.Tao

/-- Interpolation between the first absolute moment and the second moment. -/
theorem eLpNorm_le_first_second_moments {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      (∫⁻ x, ‖f x‖ₑ ∂μ) ^ ((2 - p) / p) *
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have h := ENNReal.lintegral_mul_norm_pow_le hf.enorm
    (hf.enorm.pow_const (2 : ℝ)) (show 0 ≤ 2 - p by linarith)
    (show 0 ≤ p - 1 by linarith) (show 2 - p + (p - 1) = 1 by ring)
  have heq (x : α) : ‖f x‖ₑ ^ (2 - p) * (‖f x‖ₑ ^ (2 : ℝ)) ^ (p - 1) =
      ‖f x‖ₑ ^ p := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by linarith)
      (by linarith : 0 ≤ 2 * (p - 1))]
    congr 1
    ring
  simp_rw [heq] at h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
  have hr := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1 / p)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem eLpNorm_le_real_moment_bounds {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    {p I J : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hfirst : (∫ x, |f x| ∂μ) ≤ I) (hsecond : (∫ x, f x ^ 2 ∂μ) ≤ J) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (I ^ ((2 - p) / p) * J ^ ((p - 1) / p)) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 ≤ (2 - p) / p := div_nonneg (by linarith) hp0.le
  have hb : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
  have h1 : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal I := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hfirst)
  have h2 : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≤ ENNReal.ofReal J := by
    have heq : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun x => sq_nonneg (f x))]
      apply lintegral_congr
      intro x
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal hsecond
  refine (eLpNorm_le_first_second_moments hf.aestronglyMeasurable hp hp2).trans ?_
  calc
    _ ≤ (ENNReal.ofReal I) ^ ((2 - p) / p) *
        (ENNReal.ofReal J) ^ ((p - 1) / p) :=
      mul_le_mul' (ENNReal.rpow_le_rpow h1 ha) (ENNReal.rpow_le_rpow h2 hb)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hI ha, ENNReal.ofReal_rpow_of_nonneg hJ hb,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hI _)]

theorem polynomial_interpolation_le_inverse_square {C D x a b : ℝ} {A : ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : 1 ≤ x)
    (hA : 2 * b - (A : ℝ) * a ≤ -2) :
    (C / x ^ A) ^ a * (D * x ^ 2) ^ b ≤ C ^ a * D ^ b / x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    _ = C ^ a * D ^ b * x ^ (2 * b - (A : ℝ) * a) := by
      rw [Real.div_rpow hC (pow_nonneg hx0.le _) a,
        Real.mul_rpow hD (sq_nonneg _), ← Real.rpow_natCast_mul hx0.le,
        ← Real.rpow_natCast_mul hx0.le, Real.rpow_sub hx0]
      push_cast
      ring
    _ ≤ C ^ a * D ^ b * x ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hA)
        (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hD _))
    _ = _ := by rw [Real.rpow_neg hx0.le, Real.rpow_two, div_eq_mul_inv]

#print axioms eLpNorm_le_first_second_moments
#print axioms eLpNorm_le_real_moment_bounds
#print axioms polynomial_interpolation_le_inverse_square

end Erdos1135.Tao
