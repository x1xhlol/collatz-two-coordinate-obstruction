import Erdos1135.ND.Discrepancy.EmpiricalFourier

/-!
# Finite Anchored Erdos--Turan

This file combines the checked finite Fejer kernel with the strict periodic
empirical error.  The only public discrepancy surface is the pointwise
half-open anchored bound used by the later endpoint-Dbar theorem.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory Set AddCircle

namespace Erdos1135
namespace ND

/-- The unnormalized strict empirical Fejer convolution over one symmetric
period. -/
noncomputable def ndEmpiricalFejerConvolution
    (N H : ℕ) (x : ℕ → UnitAddCircle) (y : ℝ) : ℝ :=
  ∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
    ndPeriodicStrictEmpiricalError N x (y + u) * ndFejerKernel H u

private theorem continuous_ndFejerKernel_et (H : ℕ) :
    Continuous (ndFejerKernel H) := by
  have hc : Continuous (fun x : ℝ =>
      ((H + 1 : ℕ) : ℝ) +
        2 * ∑ j ∈ Finset.range H,
          ((H - j : ℕ) : ℝ) *
            Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) := by
    fun_prop
  exact hc.congr fun x => (ndFejerKernel_eq_triangularCos H x).symm

private theorem intervalIntegrable_ndPeriodicStrictEmpiricalError_add
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y a b : ℝ) :
    IntervalIntegrable
      (fun u => ndPeriodicStrictEmpiricalError N x (y + u)) volume a b := by
  have hp := intervalIntegrable_ndPeriodicStrictEmpiricalError
    N x hN (y + a) (y + b)
  convert hp.comp_add_left y using 1 <;> ring

private theorem intervalIntegrable_ndEmpiricalFejerIntegrand
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y a b : ℝ) :
    IntervalIntegrable
      (fun u => ndPeriodicStrictEmpiricalError N x (y + u) *
        ndFejerKernel H u) volume a b := by
  exact (intervalIntegrable_ndPeriodicStrictEmpiricalError_add
    N x hN y a b).mul_continuousOn
      (continuous_ndFejerKernel_et H).continuousOn

private theorem ndEmpiricalFejerTranslated_periodic
    (N H : ℕ) (x : ℕ → UnitAddCircle) (y : ℝ) :
    Function.Periodic
      (fun t => ndPeriodicStrictEmpiricalError N x t *
        ndFejerKernel H (t - y)) 1 := by
  intro t
  change ndPeriodicStrictEmpiricalError N x (t + 1) *
      ndFejerKernel H (t + 1 - y) =
    ndPeriodicStrictEmpiricalError N x t * ndFejerKernel H (t - y)
  rw [ndPeriodicStrictEmpiricalError_periodic N x t]
  rw [show t + 1 - y = (t - y) + 1 by ring]
  rw [ndFejerKernel_periodic H (t - y)]

private theorem ndEmpiricalFejerConvolution_eq_zero_one
    (N H : ℕ) (x : ℕ → UnitAddCircle) (y : ℝ) :
    ndEmpiricalFejerConvolution N H x y =
      ∫ t in (0 : ℝ)..1,
        ndPeriodicStrictEmpiricalError N x t * ndFejerKernel H (t - y) := by
  let F : ℝ → ℝ := fun t => ndPeriodicStrictEmpiricalError N x t *
    ndFejerKernel H (t - y)
  calc
    ndEmpiricalFejerConvolution N H x y =
        ∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F (y + u) := by
          unfold ndEmpiricalFejerConvolution
          apply intervalIntegral.integral_congr
          intro u hu
          dsimp only [F]
          congr 1
          ring
    _ = ∫ t in y + (-(1 / 2 : ℝ))..y + (1 / 2 : ℝ), F t := by
          exact intervalIntegral.integral_comp_add_left F y
    _ = ∫ t in (0 : ℝ)..1, F t := by
          have hperiod :=
            (ndEmpiricalFejerTranslated_periodic N H x y).intervalIntegral_add_eq
              (y - 1 / 2) 0
          change (∫ t in y - 1 / 2..(y - 1 / 2) + 1, F t) =
            ∫ t in (0 : ℝ)..0 + 1, F t at hperiod
          convert hperiod using 1 <;> ring
    _ = ∫ t in (0 : ℝ)..1,
        ndPeriodicStrictEmpiricalError N x t * ndFejerKernel H (t - y) := rfl

private theorem ndCircleChar_coe_et (h : ℤ) (t : ℝ) :
    ndCircleChar h t = fourier h (t : UnitAddCircle) := by
  rw [fourier_coe_apply]
  rw [ndCircleChar, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem re_ndCircleChar_et (h : ℤ) (t : ℝ) :
    (ndCircleChar h t).re = Real.cos (2 * Real.pi * (h : ℝ) * t) := by
  rw [ndCircleChar, Real.fourierChar_apply]
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

private theorem ndCircleChar_sub_arg_et (h : ℤ) (t y : ℝ) :
    ndCircleChar h (t - y) = ndCircleChar (-h) y * ndCircleChar h t := by
  rw [ndCircleChar, ndCircleChar, ndCircleChar]
  simp only [Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem intervalIntegrable_fourier_mul_periodicError
    (N : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (q : ℕ) :
    IntervalIntegrable
      (fun t : ℝ => ndCircleChar (q : ℤ) t *
        (ndPeriodicStrictEmpiricalError N x t : ℂ)) volume 0 1 := by
  have hp : IntervalIntegrable
      (fun t : ℝ => (ndPeriodicStrictEmpiricalError N x t : ℂ)) volume 0 1 := by
    have hr := intervalIntegrable_ndPeriodicStrictEmpiricalError N x hN 0 1
    exact ⟨hr.1.ofReal, hr.2.ofReal⟩
  exact hp.continuousOn_mul (by
    have hc : Continuous (fun t : ℝ => ndCircleChar (q : ℤ) t) := by
      unfold ndCircleChar
      fun_prop
    exact hc.continuousOn)

private theorem intervalIntegral_periodicError_mul_cos_shift
    (N q : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y : ℝ) :
    (∫ t in (0 : ℝ)..1,
      ndPeriodicStrictEmpiricalError N x t *
        Real.cos (2 * Real.pi * (q : ℝ) * (t - y))) =
      (ndCircleChar (-(q : ℤ)) y *
        fourierCoeffOn zero_lt_one
          (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
          (-(q : ℤ))).re := by
  let g : ℝ → ℂ := fun t =>
    @fourier ((1 : ℝ) - 0) (q : ℤ)
        (t : AddCircle ((1 : ℝ) - 0)) *
      (ndPeriodicStrictEmpiricalError N x t : ℂ)
  have hg : IntervalIntegrable g volume 0 1 := by
    have hp : IntervalIntegrable
        (fun t : ℝ => (ndPeriodicStrictEmpiricalError N x t : ℂ)) volume 0 1 := by
      have hr := intervalIntegrable_ndPeriodicStrictEmpiricalError N x hN 0 1
      exact ⟨hr.1.ofReal, hr.2.ofReal⟩
    exact hp.continuousOn_mul (by
      have hc : Continuous (fun t : ℝ =>
          @fourier ((1 : ℝ) - 0) (q : ℤ)
            (t : AddCircle ((1 : ℝ) - 0))) := by fun_prop
      exact hc.continuousOn)
  have g_eq (t : ℝ) :
      g t = ndCircleChar (q : ℤ) t *
        (ndPeriodicStrictEmpiricalError N x t : ℂ) := by
    unfold g
    congr 1
    rw [fourier_coe_apply]
    rw [ndCircleChar, Real.fourierChar_apply]
    norm_num
    congr 1
    ring
  have hcoeff :
      fourierCoeffOn zero_lt_one
          (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
          (-(q : ℤ)) =
        ∫ t in (0 : ℝ)..1, g t := by
    rw [fourierCoeffOn_eq_integral]
    norm_num [g]
  have hpoint :
      (fun t : ℝ => ndPeriodicStrictEmpiricalError N x t *
        Real.cos (2 * Real.pi * (q : ℝ) * (t - y))) =
      fun t => (ndCircleChar (-(q : ℤ)) y * g t).re := by
    funext t
    rw [g_eq]
    symm
    calc
      (ndCircleChar (-(q : ℤ)) y *
          (ndCircleChar (q : ℤ) t *
            (ndPeriodicStrictEmpiricalError N x t : ℂ))).re =
          (ndCircleChar (q : ℤ) (t - y) *
            (ndPeriodicStrictEmpiricalError N x t : ℂ)).re := by
            rw [ndCircleChar_sub_arg_et]
            ring
      _ = ndPeriodicStrictEmpiricalError N x t *
          Real.cos (2 * Real.pi * (q : ℝ) * (t - y)) := by
            rw [Complex.mul_re]
            simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            rw [re_ndCircleChar_et]
            push_cast
            rw [mul_comm]
  rw [hpoint]
  have hre :
      (∫ t in (0 : ℝ)..1, (ndCircleChar (-(q : ℤ)) y * g t).re) =
        (∫ t in (0 : ℝ)..1, ndCircleChar (-(q : ℤ)) y * g t).re := by
    exact intervalIntegral.intervalIntegral_re
      (hg.const_mul (ndCircleChar (-(q : ℤ)) y))
  have hmul :
      (∫ t in (0 : ℝ)..1, ndCircleChar (-(q : ℤ)) y * g t) =
        ndCircleChar (-(q : ℤ)) y * ∫ t in (0 : ℝ)..1, g t := by
    exact intervalIntegral.integral_const_mul _ _
  rw [hre]
  rw [hmul]
  rw [← hcoeff]

private theorem intervalIntegrable_periodicError_mul_cos
    (N q : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ndPeriodicStrictEmpiricalError N x t *
        Real.cos (2 * Real.pi * (q : ℝ) * (t - y))) volume 0 1 := by
  exact (intervalIntegrable_ndPeriodicStrictEmpiricalError N x hN 0 1).mul_continuousOn
    (by fun_prop)

private theorem ndEmpiricalFejerConvolution_eq_modeSum
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y : ℝ) :
    ndEmpiricalFejerConvolution N H x y =
      2 * ∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          (ndCircleChar (-((j + 1 : ℕ) : ℤ)) y *
            fourierCoeffOn zero_lt_one
              (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
              (-((j + 1 : ℕ) : ℤ))).re := by
  let P : ℝ → ℝ := ndPeriodicStrictEmpiricalError N x
  let mode : ℕ → ℝ → ℝ := fun j t =>
    ((H - j : ℕ) : ℝ) *
      (P t * Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * (t - y)))
  have hp : IntervalIntegrable P volume 0 1 :=
    intervalIntegrable_ndPeriodicStrictEmpiricalError N x hN 0 1
  have hmode (j : ℕ) : IntervalIntegrable (mode j) volume 0 1 := by
    exact (intervalIntegrable_periodicError_mul_cos N (j + 1) x hN y).const_mul
      ((H - j : ℕ) : ℝ)
  have hmodes : IntervalIntegrable
      (fun t => ∑ j ∈ Finset.range H, mode j t) volume 0 1 := by
    let s := Finset.range H
    change IntervalIntegrable (fun t => ∑ j ∈ s, mode j t) volume 0 1
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hmode a).add ih
  rw [ndEmpiricalFejerConvolution_eq_zero_one]
  calc
    (∫ t in (0 : ℝ)..1, P t * ndFejerKernel H (t - y)) =
        ∫ t in (0 : ℝ)..1,
          ((H + 1 : ℕ) : ℝ) * P t +
            2 * ∑ j ∈ Finset.range H, mode j t := by
          apply intervalIntegral.integral_congr
          intro t ht
          change P t * ndFejerKernel H (t - y) =
            ((H + 1 : ℕ) : ℝ) * P t +
              2 * ∑ j ∈ Finset.range H, mode j t
          rw [ndFejerKernel_eq_triangularCos]
          have hsum :
              (∑ j ∈ Finset.range H, mode j t) =
                P t * ∑ j ∈ Finset.range H,
                  ((H - j : ℕ) : ℝ) *
                    Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * (t - y)) := by
            unfold mode
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          rw [hsum]
          ring
    _ = ((H + 1 : ℕ) : ℝ) * (∫ t in (0 : ℝ)..1, P t) +
          2 * ∑ j ∈ Finset.range H, ∫ t in (0 : ℝ)..1, mode j t := by
          rw [intervalIntegral.integral_add (hp.const_mul _) (hmodes.const_mul 2)]
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral.integral_finset_sum]
          intro j hj
          exact hmode j
    _ = 2 * ∑ j ∈ Finset.range H, ∫ t in (0 : ℝ)..1, mode j t := by
          rw [show (∫ t in (0 : ℝ)..1, P t) = 0 by
            exact intervalIntegral_ndPeriodicStrictEmpiricalError N x hN]
          ring
    _ = 2 * ∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          (ndCircleChar (-((j + 1 : ℕ) : ℤ)) y *
            fourierCoeffOn zero_lt_one
              (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
              (-((j + 1 : ℕ) : ℤ))).re := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          unfold mode
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral_periodicError_mul_cos_shift N (j + 1) x hN y]

private theorem norm_ndCircleChar_et (h : ℤ) (t : ℝ) :
    ‖ndCircleChar h t‖ = 1 := by
  exact Circle.norm_coe _

private theorem abs_ndEmpiricalFejerConvolution_le_coeffSum
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y : ℝ) :
    |ndEmpiricalFejerConvolution N H x y| ≤
      2 * ∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          ‖fourierCoeffOn zero_lt_one
            (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
            (-((j + 1 : ℕ) : ℤ))‖ := by
  rw [ndEmpiricalFejerConvolution_eq_modeSum N H x hN y]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          (ndCircleChar (-((j + 1 : ℕ) : ℤ)) y *
            fourierCoeffOn zero_lt_one
              (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
              (-((j + 1 : ℕ) : ℤ))).re| ≤
        ∑ j ∈ Finset.range H,
          |((H - j : ℕ) : ℝ) *
            (ndCircleChar (-((j + 1 : ℕ) : ℤ)) y *
              fourierCoeffOn zero_lt_one
                (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
                (-((j + 1 : ℕ) : ℤ))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          ‖fourierCoeffOn zero_lt_one
            (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
            (-((j + 1 : ℕ) : ℤ))‖ := by
      gcongr with j hj
      rw [abs_mul, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ ((H - j : ℕ) : ℝ))]
      gcongr
      calc
        |(ndCircleChar (-((j + 1 : ℕ) : ℤ)) y *
            fourierCoeffOn zero_lt_one
              (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
              (-((j + 1 : ℕ) : ℤ))).re| ≤
            ‖ndCircleChar (-((j + 1 : ℕ) : ℤ)) y *
              fourierCoeffOn zero_lt_one
                (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
                (-((j + 1 : ℕ) : ℤ))‖ := Complex.abs_re_le_norm _
        _ = ‖fourierCoeffOn zero_lt_one
              (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
              (-((j + 1 : ℕ) : ℤ))‖ := by
            rw [norm_mul, norm_ndCircleChar_et, one_mul]

private theorem abs_ndEmpiricalFejerConvolution_le_characterSum
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N)
    (y : ℝ) :
    |ndEmpiricalFejerConvolution N H x y| ≤
      (1 / Real.pi) * ∑ j ∈ Finset.range H,
        (((H - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) *
          ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
  calc
    |ndEmpiricalFejerConvolution N H x y| ≤
        2 * ∑ j ∈ Finset.range H,
          ((H - j : ℕ) : ℝ) *
            ‖fourierCoeffOn zero_lt_one
              (fun t => (ndPeriodicStrictEmpiricalError N x t : ℂ))
              (-((j + 1 : ℕ) : ℤ))‖ :=
      abs_ndEmpiricalFejerConvolution_le_coeffSum N H x hN y
    _ = (1 / Real.pi) * ∑ j ∈ Finset.range H,
        (((H - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) *
          ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_fourierCoeffOn_ndPeriodicStrictEmpiricalError_neg_nat
        N (j + 1) x hN (by omega)]
      have hq : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero, hq]

private theorem intervalIntegrable_ndFejerKernel_et
    (H : ℕ) (a b : ℝ) :
    IntervalIntegrable (ndFejerKernel H) volume a b :=
  (continuous_ndFejerKernel_et H).intervalIntegrable a b

private theorem intervalIntegral_ndFejerKernel_symmetric (H : ℕ) :
    (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ndFejerKernel H u) =
      (H + 1 : ℕ) := by
  calc
    (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ndFejerKernel H u) =
        ∫ u in (0 : ℝ)..1, ndFejerKernel H u := by
      have hperiod := (ndFejerKernel_periodic H).intervalIntegral_add_eq
        (-(1 / 2 : ℝ)) 0
      convert hperiod using 1 <;> ring
    _ = (H + 1 : ℕ) := intervalIntegral_ndFejerKernel H

private theorem intervalIntegral_ndFejerKernel_neg_tail
    (H : ℕ) (D : ℝ) :
    (∫ u in (-(1 / 2 : ℝ))..(-D / 2), ndFejerKernel H u) =
      ∫ u in D / 2..(1 / 2 : ℝ), ndFejerKernel H u := by
  calc
    (∫ u in (-(1 / 2 : ℝ))..(-D / 2), ndFejerKernel H u) =
        ∫ u in (-(1 / 2 : ℝ))..(-D / 2), ndFejerKernel H (-u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact (ndFejerKernel_even H u).symm
    _ = ∫ u in D / 2..(1 / 2 : ℝ), ndFejerKernel H u := by
      convert intervalIntegral.integral_comp_neg
        (f := ndFejerKernel H) (a := (-(1 / 2 : ℝ))) (b := -D / 2) using 1 <;> ring

private theorem intervalIntegral_ndFejerKernel_center
    (H : ℕ) (D : ℝ) :
    (∫ u in -D / 2..D / 2, ndFejerKernel H u) =
      ((H + 1 : ℕ) : ℝ) -
        2 * ∫ u in D / 2..(1 / 2 : ℝ), ndFejerKernel H u := by
  have hL := intervalIntegrable_ndFejerKernel_et H (-(1 / 2 : ℝ)) (-D / 2)
  have hC := intervalIntegrable_ndFejerKernel_et H (-D / 2) (D / 2)
  have hLC := intervalIntegrable_ndFejerKernel_et H (-(1 / 2 : ℝ)) (D / 2)
  have hR := intervalIntegrable_ndFejerKernel_et H (D / 2) (1 / 2)
  have hsplit :
      (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ndFejerKernel H u) =
        (∫ u in (-(1 / 2 : ℝ))..(-D / 2), ndFejerKernel H u) +
          (∫ u in -D / 2..D / 2, ndFejerKernel H u) +
            ∫ u in D / 2..(1 / 2 : ℝ), ndFejerKernel H u := by
    calc
      (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ndFejerKernel H u) =
          (∫ u in (-(1 / 2 : ℝ))..D / 2, ndFejerKernel H u) +
            ∫ u in D / 2..(1 / 2 : ℝ), ndFejerKernel H u :=
        (intervalIntegral.integral_add_adjacent_intervals hLC hR).symm
      _ = ((∫ u in (-(1 / 2 : ℝ))..(-D / 2), ndFejerKernel H u) +
            ∫ u in -D / 2..D / 2, ndFejerKernel H u) +
            ∫ u in D / 2..(1 / 2 : ℝ), ndFejerKernel H u := by
        rw [intervalIntegral.integral_add_adjacent_intervals hL hC]
  rw [intervalIntegral_ndFejerKernel_symmetric H,
    intervalIntegral_ndFejerKernel_neg_tail H D] at hsplit
  linarith

private theorem intervalIntegral_mul_ndFejerKernel_center_zero
    (H : ℕ) (D : ℝ) :
    (∫ u in -D / 2..D / 2, u * ndFejerKernel H u) = 0 := by
  let f : ℝ → ℝ := fun u => u * ndFejerKernel H u
  have hcomp :
      (∫ u in -D / 2..D / 2, f (-u)) =
        ∫ u in -D / 2..D / 2, f u := by
    convert intervalIntegral.integral_comp_neg
      (f := f) (a := -D / 2) (b := D / 2) using 1 <;> ring
  have hneg :
      (∫ u in -D / 2..D / 2, f (-u)) =
        -(∫ u in -D / 2..D / 2, f u) := by
    calc
      (∫ u in -D / 2..D / 2, f (-u)) =
          ∫ u in -D / 2..D / 2, -f u := by
        apply intervalIntegral.integral_congr
        intro u hu
        unfold f
        change (-u) * ndFejerKernel H (-u) =
          -(u * ndFejerKernel H u)
        rw [ndFejerKernel_even H u]
        ring
      _ = -(∫ u in -D / 2..D / 2, f u) :=
        intervalIntegral.integral_neg
  change (∫ u in -D / 2..D / 2, f u) = 0
  linarith

private theorem fejer_wedge_integral_lower
    (H : ℕ) (A s : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (F : ℝ → ℝ)
    (hF : ∀ a b : ℝ, IntervalIntegrable F volume a b)
    (hglobal : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), -A ≤ F u)
    (hcenter : ∀ u ∈ Set.Ioo (-A / 2) (A / 2), A / 2 + s * u ≤ F u) :
    A * ((H + 1 : ℕ) : ℝ) / 2 - 3 / 2 ≤
      ∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F u * ndFejerKernel H u := by
  let T : ℝ := ∫ u in A / 2..(1 / 2 : ℝ), ndFejerKernel H u
  have hL : (-(1 / 2 : ℝ)) ≤ -A / 2 := by linarith
  have hC : -A / 2 ≤ A / 2 := by linarith
  have hR : A / 2 ≤ (1 / 2 : ℝ) := by linarith
  have hK (a b : ℝ) := intervalIntegrable_ndFejerKernel_et H a b
  have hFK (a b : ℝ) : IntervalIntegrable
      (fun u => F u * ndFejerKernel H u) volume a b :=
    (hF a b).mul_continuousOn (continuous_ndFejerKernel_et H).continuousOn
  have htailLower (a b : ℝ) : IntervalIntegrable
      (fun u => (-A) * ndFejerKernel H u) volume a b :=
    (hK a b).const_mul (-A)
  have hcenterLower : IntervalIntegrable
      (fun u => (A / 2 + s * u) * ndFejerKernel H u)
      volume (-A / 2) (A / 2) := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun u : ℝ => A / 2 + s * u)).mul
      (continuous_ndFejerKernel_et H)
  have hleft :
      (∫ u in (-(1 / 2 : ℝ))..(-A / 2),
          (-A) * ndFejerKernel H u) ≤
        ∫ u in (-(1 / 2 : ℝ))..(-A / 2),
          F u * ndFejerKernel H u := by
    apply intervalIntegral.integral_mono_on hL
      (htailLower _ _) (hFK _ _)
    intro u hu
    apply mul_le_mul_of_nonneg_right
    · exact hglobal u ⟨hu.1, hu.2.trans (hC.trans hR)⟩
    · exact ndFejerKernel_nonneg H u
  have hmiddle :
      (∫ u in -A / 2..A / 2,
          (A / 2 + s * u) * ndFejerKernel H u) ≤
        ∫ u in -A / 2..A / 2,
          F u * ndFejerKernel H u := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hC
      hcenterLower (hFK _ _)
    intro u hu
    exact mul_le_mul_of_nonneg_right (hcenter u hu)
      (ndFejerKernel_nonneg H u)
  have hright :
      (∫ u in A / 2..(1 / 2 : ℝ),
          (-A) * ndFejerKernel H u) ≤
        ∫ u in A / 2..(1 / 2 : ℝ),
          F u * ndFejerKernel H u := by
    apply intervalIntegral.integral_mono_on hR
      (htailLower _ _) (hFK _ _)
    intro u hu
    apply mul_le_mul_of_nonneg_right
    · exact hglobal u ⟨hL.trans (hC.trans hu.1), hu.2⟩
    · exact ndFejerKernel_nonneg H u
  have hsplit :
      (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          F u * ndFejerKernel H u) =
        (∫ u in (-(1 / 2 : ℝ))..(-A / 2),
            F u * ndFejerKernel H u) +
          (∫ u in -A / 2..A / 2, F u * ndFejerKernel H u) +
            ∫ u in A / 2..(1 / 2 : ℝ), F u * ndFejerKernel H u := by
    calc
      (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F u * ndFejerKernel H u) =
          (∫ u in (-(1 / 2 : ℝ))..A / 2, F u * ndFejerKernel H u) +
            ∫ u in A / 2..(1 / 2 : ℝ), F u * ndFejerKernel H u :=
        (intervalIntegral.integral_add_adjacent_intervals (hFK _ _) (hFK _ _)).symm
      _ = ((∫ u in (-(1 / 2 : ℝ))..(-A / 2), F u * ndFejerKernel H u) +
            ∫ u in -A / 2..A / 2, F u * ndFejerKernel H u) +
            ∫ u in A / 2..(1 / 2 : ℝ), F u * ndFejerKernel H u := by
        exact congrArg (fun z => z +
          ∫ u in A / 2..(1 / 2 : ℝ), F u * ndFejerKernel H u)
          (intervalIntegral.integral_add_adjacent_intervals
            (hFK (-(1 / 2 : ℝ)) (-A / 2)) (hFK (-A / 2) (A / 2))).symm
  have hlowerSum :
      (∫ u in (-(1 / 2 : ℝ))..(-A / 2),
          (-A) * ndFejerKernel H u) +
        (∫ u in -A / 2..A / 2,
          (A / 2 + s * u) * ndFejerKernel H u) +
        (∫ u in A / 2..(1 / 2 : ℝ),
          (-A) * ndFejerKernel H u) ≤
        ∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          F u * ndFejerKernel H u := by
    rw [hsplit]
    linarith
  have hleftEval :
      (∫ u in (-(1 / 2 : ℝ))..(-A / 2),
          (-A) * ndFejerKernel H u) = (-A) * T := by
    rw [intervalIntegral.integral_const_mul]
    exact congrArg ((-A) * ·)
      (intervalIntegral_ndFejerKernel_neg_tail H A)
  have hrightEval :
      (∫ u in A / 2..(1 / 2 : ℝ),
          (-A) * ndFejerKernel H u) = (-A) * T := by
    rw [intervalIntegral.integral_const_mul]
  have huK : IntervalIntegrable
      (fun u : ℝ => u * ndFejerKernel H u) volume (-A / 2) (A / 2) := by
    apply Continuous.intervalIntegrable
    exact continuous_id.mul (continuous_ndFejerKernel_et H)
  have hmiddleEval :
      (∫ u in -A / 2..A / 2,
          (A / 2 + s * u) * ndFejerKernel H u) =
        (A / 2) * (((H + 1 : ℕ) : ℝ) - 2 * T) := by
    calc
      (∫ u in -A / 2..A / 2,
          (A / 2 + s * u) * ndFejerKernel H u) =
          ∫ u in -A / 2..A / 2,
            (A / 2) * ndFejerKernel H u +
              s * (u * ndFejerKernel H u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = (A / 2) * (∫ u in -A / 2..A / 2, ndFejerKernel H u) +
          s * (∫ u in -A / 2..A / 2, u * ndFejerKernel H u) := by
        rw [intervalIntegral.integral_add
          ((hK _ _).const_mul (A / 2)) (huK.const_mul s)]
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const_mul]
      _ = (A / 2) * (((H + 1 : ℕ) : ℝ) - 2 * T) := by
        rw [intervalIntegral_ndFejerKernel_center H A,
          intervalIntegral_mul_ndFejerKernel_center_zero H A]
        ring
  have htailPack := intervalIntegral_ndFejerKernel_tail_le H A hA hA1
  have hT : T ≤ 1 / (2 * A) := htailPack.1.trans htailPack.2
  have hAT : A * T ≤ 1 / 2 := by
    calc
      A * T ≤ A * (1 / (2 * A)) :=
        mul_le_mul_of_nonneg_left hT hA.le
      _ = 1 / 2 := by field_simp [hA.ne']
  rw [hleftEval, hmiddleEval, hrightEval] at hlowerSum
  nlinarith

private theorem exists_ndEmpiricalFejerConvolution_large
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) :
    ∃ y : ℝ,
      ndEmpiricalAmplitude N x * ((H + 1 : ℕ) : ℝ) / 2 - 3 / 2 ≤
        |ndEmpiricalFejerConvolution N H x y| := by
  let A : ℝ := ndEmpiricalAmplitude N x
  by_cases hAz : A = 0
  · refine ⟨0, ?_⟩
    change A * ((H + 1 : ℕ) : ℝ) / 2 - 3 / 2 ≤
      |ndEmpiricalFejerConvolution N H x 0|
    rw [hAz]
    have habs := abs_nonneg (ndEmpiricalFejerConvolution N H x 0)
    linarith
  have hA : 0 < A := lt_of_le_of_ne
    (ndEmpiricalAmplitude_nonneg N x) (Ne.symm hAz)
  have hAhalf : A ≤ 1 / 2 := ndEmpiricalAmplitude_le_half N x
  have hA1 : A ≤ 1 := hAhalf.trans (by norm_num)
  obtain ⟨b, hbNode, hneg | hpos⟩ := exists_ndEmpirical_extremal N x
  · let y : ℝ := b - A / 2
    change ndCenteredStrictEmpiricalError N x b = -A at hneg
    let F : ℝ → ℝ := fun u =>
      -ndPeriodicStrictEmpiricalError N x (y + u)
    have hF : ∀ a c : ℝ, IntervalIntegrable F volume a c := by
      intro a c
      exact (intervalIntegrable_ndPeriodicStrictEmpiricalError_add
        N x hN y a c).neg
    have hglobal : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), -A ≤ F u := by
      intro u hu
      have hp := abs_ndPeriodicStrictEmpiricalError_le_amplitude
        N x hN (y + u)
      exact (abs_le.mp hp).2 |> fun h => by
        unfold F
        linarith
    have hcenter : ∀ u ∈ Set.Ioo (-A / 2) (A / 2),
        A / 2 + (1 : ℝ) * u ≤ F u := by
      intro u hu
      let d : ℝ := A / 2 - u
      have hd : d ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · unfold d
          linarith [hu.2]
        · unfold d
          linarith [hu.1, hAhalf]
      have hs := neg_centeredStrict_sub_le_neg_periodic_sub
        N x b d hN (ndEmpiricalNodes_subset_Icc N x hbNode) hd
      rw [hneg] at hs
      change A / 2 + (1 : ℝ) * u ≤
        -ndPeriodicStrictEmpiricalError N x (y + u)
      convert hs using 1
      · unfold d
        ring
      · unfold d y
        ring
    have hwedge := fejer_wedge_integral_lower H A 1 hA hA1 F hF hglobal hcenter
    have hconv :
        (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F u * ndFejerKernel H u) =
          -ndEmpiricalFejerConvolution N H x y := by
      calc
        (∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F u * ndFejerKernel H u) =
            ∫ u in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
              -(ndPeriodicStrictEmpiricalError N x (y + u) *
                ndFejerKernel H u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          unfold F
          ring
        _ = -ndEmpiricalFejerConvolution N H x y := by
          rw [intervalIntegral.integral_neg]
          rfl
    refine ⟨y, ?_⟩
    rw [hconv] at hwedge
    exact hwedge.trans (neg_le_abs _)
  · let y : ℝ := b + A / 2
    change ndCenteredWeakEmpiricalError N x b = A at hpos
    let F : ℝ → ℝ := fun u =>
      ndPeriodicStrictEmpiricalError N x (y + u)
    have hF : ∀ a c : ℝ, IntervalIntegrable F volume a c := by
      intro a c
      exact intervalIntegrable_ndPeriodicStrictEmpiricalError_add
        N x hN y a c
    have hglobal : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), -A ≤ F u := by
      intro u hu
      exact (abs_le.mp (abs_ndPeriodicStrictEmpiricalError_le_amplitude
        N x hN (y + u))).1
    have hcenter : ∀ u ∈ Set.Ioo (-A / 2) (A / 2),
        A / 2 + (-1 : ℝ) * u ≤ F u := by
      intro u hu
      let d : ℝ := A / 2 + u
      have hd : d ∈ Set.Ioc (0 : ℝ) 1 := by
        constructor
        · unfold d
          linarith [hu.1]
        · unfold d
          linarith [hu.2, hAhalf]
      have hs := ndCenteredWeakEmpiricalError_sub_le_periodic_add
        N x b d hN (ndEmpiricalNodes_subset_Icc N x hbNode) hd
      rw [hpos] at hs
      change A / 2 + (-1 : ℝ) * u ≤
        ndPeriodicStrictEmpiricalError N x (y + u)
      convert hs using 1
      · unfold d
        ring
      · unfold d y
        ring
    have hwedge := fejer_wedge_integral_lower H A (-1) hA hA1
      F hF hglobal hcenter
    refine ⟨y, ?_⟩
    change A * ((H + 1 : ℕ) : ℝ) / 2 - 3 / 2 ≤
      |ndEmpiricalFejerConvolution N H x y|
    exact hwedge.trans (le_abs_self _)

/-- The sharp finite Erdős--Turán estimate for the centered empirical
amplitude.  The summation index `j` represents the frequency `j + 1`. -/
theorem ndEmpiricalAmplitude_le_erdosTuran
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (hH : 0 < H) :
    ndEmpiricalAmplitude N x ≤
      3 / (((H + 1 : ℕ) : ℝ)) +
        (2 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
  let A : ℝ := ndEmpiricalAmplitude N x
  let S : ℝ := ∑ j ∈ Finset.range H,
    (((H - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) *
      ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖
  let W : ℝ := ∑ j ∈ Finset.range H,
    (1 / (((j + 1 : ℕ) : ℝ)) -
        1 / (((H + 1 : ℕ) : ℝ))) *
      ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖
  have hH1 : 0 < (((H + 1 : ℕ) : ℝ)) := by positivity
  have hH1ne : (((H + 1 : ℕ) : ℝ)) ≠ 0 := hH1.ne'
  have hweight (j : ℕ) (hj : j ∈ Finset.range H) :
      (((H - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) /
          (((H + 1 : ℕ) : ℝ)) =
        1 / (((j + 1 : ℕ) : ℝ)) -
          1 / (((H + 1 : ℕ) : ℝ)) := by
    have hjle : j ≤ H := (Finset.mem_range.mp hj).le
    have hq : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [Nat.cast_sub hjle]
    push_cast
    field_simp [hq, hH1ne]
    ring
  have hSW : S / (((H + 1 : ℕ) : ℝ)) = W := by
    unfold S W
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      ((((H - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) *
          ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖) /
            (((H + 1 : ℕ) : ℝ)) =
          ((((H - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) /
              (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by ring
      _ = (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
          rw [hweight j hj]
  obtain ⟨y, hlower⟩ := exists_ndEmpiricalFejerConvolution_large N H x hN
  have hupper := abs_ndEmpiricalFejerConvolution_le_characterSum N H x hN y
  have hraw :
      A * (((H + 1 : ℕ) : ℝ)) / 2 - 3 / 2 ≤ (1 / Real.pi) * S := by
    exact hlower.trans hupper
  have hnum :
      A * (((H + 1 : ℕ) : ℝ)) ≤ 3 + (2 / Real.pi) * S := by
    have htwice := mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 2)
    calc
      A * (((H + 1 : ℕ) : ℝ)) =
          2 * (A * (((H + 1 : ℕ) : ℝ)) / 2 - 3 / 2) + 3 := by ring
      _ ≤ 2 * ((1 / Real.pi) * S) + 3 := add_le_add_left htwice 3
      _ = 3 + (2 / Real.pi) * S := by ring
  change A ≤ 3 / (((H + 1 : ℕ) : ℝ)) + (2 / Real.pi) * W
  calc
    A = (A * (((H + 1 : ℕ) : ℝ))) / (((H + 1 : ℕ) : ℝ)) := by
      field_simp [hH1ne]
    _ ≤ (3 + (2 / Real.pi) * S) / (((H + 1 : ℕ) : ℝ)) :=
      (div_le_div_iff_of_pos_right hH1).2 hnum
    _ = 3 / (((H + 1 : ℕ) : ℝ)) +
        (2 / Real.pi) * (S / (((H + 1 : ℕ) : ℝ))) := by ring
    _ = 3 / (((H + 1 : ℕ) : ℝ)) + (2 / Real.pi) * W := by rw [hSW]

/-- The sharp pointwise half-open anchored Erdős--Turán estimate. -/
theorem abs_ndStrictEmpiricalError_le_erdosTuran_sharp
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (hH : 0 < H)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndStrictEmpiricalError N x t| ≤
      6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
  have hamp := ndEmpiricalAmplitude_le_erdosTuran N H x hN hH
  have htA := abs_ndCenteredStrictEmpiricalError_le_amplitude N x t ht
  have hzeroA := abs_ndCenteredStrictEmpiricalError_le_amplitude N x 0 (by norm_num)
  rw [ndStrictEmpiricalError_eq_centered_sub_zero]
  calc
    |ndCenteredStrictEmpiricalError N x t -
        ndCenteredStrictEmpiricalError N x 0| ≤
        |ndCenteredStrictEmpiricalError N x t| +
          |ndCenteredStrictEmpiricalError N x 0| := abs_sub _ _
    _ ≤ 2 * ndEmpiricalAmplitude N x := by linarith
    _ ≤ 2 * (3 / (((H + 1 : ℕ) : ℝ)) +
        (2 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖) :=
      mul_le_mul_of_nonneg_left hamp (by norm_num)
    _ = 6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ)) -
              1 / (((H + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by ring

/-- The deliberately weakened pointwise Erdős--Turán estimate consumed by
the later discrepancy-to-phase-gap adapter. -/
theorem abs_ndStrictEmpiricalError_le_erdosTuran
    (N H : ℕ) (x : ℕ → UnitAddCircle) (hN : 0 < N) (hH : 0 < H)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |ndStrictEmpiricalError N x t| ≤
      6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
  calc
    |ndStrictEmpiricalError N x t| ≤
        6 / (((H + 1 : ℕ) : ℝ)) +
          (4 / Real.pi) * ∑ j ∈ Finset.range H,
            (1 / (((j + 1 : ℕ) : ℝ)) -
                1 / (((H + 1 : ℕ) : ℝ))) *
              ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ :=
      abs_ndStrictEmpiricalError_le_erdosTuran_sharp N H x hN hH t ht
    _ ≤ 6 / (((H + 1 : ℕ) : ℝ)) +
        (4 / Real.pi) * ∑ j ∈ Finset.range H,
          (1 / (((j + 1 : ℕ) : ℝ))) *
            ‖ndEmpiricalCharacterAverage N x ((j + 1 : ℕ) : ℤ)‖ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hH1inv : 0 ≤ 1 / (((H + 1 : ℕ) : ℝ)) := by positivity
      linarith

end ND
end Erdos1135
