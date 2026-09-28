import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Finite Fejer Kernel

This file provides the unnormalized finite Fejer kernel needed by the later
Erdos--Turan argument. The parameter `H` is the largest positive frequency,
so the defining character sum has `H + 1` terms and total mass `H + 1`.
-/

open scoped BigOperators FourierTransform
open ComplexConjugate MeasureTheory

namespace Erdos1135
namespace ND

/-- The analyst's period-one circle character at integer frequency `h`. -/
noncomputable def ndCircleChar (h : ℤ) (x : ℝ) : ℂ :=
  (Real.fourierChar ((h : ℝ) * x) : ℂ)

/-- The unnormalized one-sided character sum with frequencies `0, ..., H`. -/
noncomputable def ndFejerSum (H : ℕ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (H + 1), ndCircleChar (r : ℤ) x

/-- The unnormalized finite Fejer kernel. -/
noncomputable def ndFejerKernel (H : ℕ) (x : ℝ) : ℝ :=
  Complex.normSq (ndFejerSum H x)

private theorem ndCircleChar_add (h k : ℤ) (x : ℝ) :
    ndCircleChar (h + k) x = ndCircleChar h x * ndCircleChar k x := by
  simp only [ndCircleChar]
  rw [Int.cast_add, add_mul]
  exact_mod_cast AddChar.map_add_eq_mul Real.fourierChar ((h : ℝ) * x) ((k : ℝ) * x)

private theorem ndCircleChar_neg (h : ℤ) (x : ℝ) :
    ndCircleChar (-h) x = conj (ndCircleChar h x) := by
  change ((Real.fourierChar (((-h : ℤ) : ℝ) * x) : Circle) : ℂ) =
    conj (((Real.fourierChar ((h : ℝ) * x) : Circle) : ℂ))
  rw [← Circle.coe_inv_eq_conj]
  congr 1
  simpa only [Int.cast_neg, neg_mul] using
    (AddChar.map_neg_eq_inv Real.fourierChar ((h : ℝ) * x))

private theorem ndCircleChar_sub (h k : ℤ) (x : ℝ) :
    ndCircleChar h x * conj (ndCircleChar k x) = ndCircleChar (h - k) x := by
  rw [← ndCircleChar_neg, ← ndCircleChar_add]
  rfl

private theorem norm_ndCircleChar (h : ℤ) (x : ℝ) :
    ‖ndCircleChar h x‖ = 1 := by
  exact Circle.norm_coe _

private theorem re_ndCircleChar (h : ℤ) (x : ℝ) :
    (ndCircleChar h x).re = Real.cos (2 * Real.pi * (h : ℝ) * x) := by
  rw [ndCircleChar, Real.fourierChar_apply]
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

private theorem ndCircleChar_add_one (h : ℤ) (x : ℝ) :
    ndCircleChar h (x + 1) = ndCircleChar h x := by
  rw [ndCircleChar, ndCircleChar, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [show (((2 * Real.pi * ((h : ℝ) * (x + 1)) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * ((h : ℝ) * x) : ℝ) : ℂ) * Complex.I) +
        (h : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem ndCircleChar_neg_arg (h : ℤ) (x : ℝ) :
    ndCircleChar h (-x) = conj (ndCircleChar h x) := by
  rw [show ndCircleChar h (-x) = ndCircleChar (-h) x by
    simp only [ndCircleChar]
    congr 2
    push_cast
    ring]
  exact ndCircleChar_neg h x

private theorem continuous_ndCircleChar (h : ℤ) : Continuous (ndCircleChar h) := by
  unfold ndCircleChar
  fun_prop

private theorem continuous_ndFejerSum (H : ℕ) : Continuous (ndFejerSum H) := by
  unfold ndFejerSum
  exact continuous_finset_sum _ fun i hi => continuous_ndCircleChar (i : ℤ)

private theorem continuous_ndFejerKernel (H : ℕ) : Continuous (ndFejerKernel H) := by
  unfold ndFejerKernel
  exact Complex.continuous_normSq.comp (continuous_ndFejerSum H)

/-- The Fejer kernel is nonnegative. -/
theorem ndFejerKernel_nonneg (H : ℕ) (x : ℝ) :
    0 ≤ ndFejerKernel H x := by
  exact Complex.normSq_nonneg _

/-- The Fejer kernel has period one. -/
theorem ndFejerKernel_periodic (H : ℕ) :
    Function.Periodic (ndFejerKernel H) 1 := by
  intro x
  rw [ndFejerKernel, ndFejerKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact ndCircleChar_add_one (r : ℤ) x

/-- The Fejer kernel is even. -/
theorem ndFejerKernel_even (H : ℕ) : Function.Even (ndFejerKernel H) := by
  intro x
  rw [ndFejerKernel, ndFejerKernel]
  have hsum : ndFejerSum H (-x) = conj (ndFejerSum H x) := by
    simp only [ndFejerSum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    exact ndCircleChar_neg_arg (r : ℤ) x
  rw [hsum, Complex.normSq_conj]

private theorem ndFejerSum_succ (H : ℕ) (x : ℝ) :
    ndFejerSum (H + 1) x = ndFejerSum H x + ndCircleChar (H + 1 : ℕ) x := by
  simp [ndFejerSum, Finset.sum_range_succ]

private theorem re_char_mul_conj_last
    (H r : ℕ) (hr : r < H + 1) (x : ℝ) :
    (ndCircleChar (r : ℤ) x * conj (ndCircleChar (H + 1 : ℕ) x)).re =
      Real.cos (2 * Real.pi * ((H - r + 1 : ℕ) : ℝ) * x) := by
  have hdiff : (r : ℤ) - (H + 1 : ℕ) = -((H - r + 1 : ℕ) : ℤ) := by
    omega
  rw [ndCircleChar_sub, re_ndCircleChar, hdiff]
  push_cast
  rw [show 2 * Real.pi * (-(((H - r : ℕ) : ℝ) + 1)) * x =
      -(2 * Real.pi * (((H - r : ℕ) : ℝ) + 1) * x) by ring, Real.cos_neg]

private theorem re_ndFejerSum_mul_conj_last (H : ℕ) (x : ℝ) :
    (ndFejerSum H x * conj (ndCircleChar (H + 1 : ℕ) x)).re =
      ∑ j ∈ Finset.range (H + 1),
        Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) := by
  rw [ndFejerSum, Finset.sum_mul, Complex.re_sum]
  calc
    ∑ r ∈ Finset.range (H + 1),
        (ndCircleChar (r : ℤ) x * conj (ndCircleChar (H + 1 : ℕ) x)).re
      = ∑ r ∈ Finset.range (H + 1),
          Real.cos (2 * Real.pi * ((H - r + 1 : ℕ) : ℝ) * x) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact re_char_mul_conj_last H r (Finset.mem_range.mp hr) x
    _ = ∑ j ∈ Finset.range (H + 1),
          Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) := by
          rw [← Finset.sum_range_reflect
            (fun j => Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) (H + 1)]
          apply Finset.sum_congr rfl
          intro r hr
          congr 1

private theorem ndWeightedCosSum_succ (H : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (H + 1),
        ((H + 1 - j : ℕ) : ℝ) *
          Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) =
      (∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) +
      ∑ j ∈ Finset.range (H + 1),
        Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
  have hsum :
      (∑ j ∈ Finset.range H,
        ((H + 1 - j : ℕ) : ℝ) *
          Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) =
      (∑ j ∈ Finset.range H,
        ((H - j : ℕ) : ℝ) *
          Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) +
      ∑ j ∈ Finset.range H,
        Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < H := Finset.mem_range.mp hj
    have hnat : H + 1 - j = (H - j) + 1 := by
      omega
    rw [hnat, Nat.cast_add, Nat.cast_one]
    ring
  rw [hsum]
  ring

private theorem ndFejerKernel_succ (H : ℕ) (x : ℝ) :
    ndFejerKernel (H + 1) x =
      ndFejerKernel H x + 1 +
        2 * ∑ j ∈ Finset.range (H + 1),
          Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) := by
  rw [ndFejerKernel, ndFejerSum_succ, Complex.normSq_add,
    re_ndFejerSum_mul_conj_last]
  have hnormsq : Complex.normSq (ndCircleChar (H + 1 : ℕ) x) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_ndCircleChar]
    norm_num
  rw [hnormsq]
  rfl

/-- The exact triangular cosine expansion of the unnormalized Fejer kernel. -/
theorem ndFejerKernel_eq_triangularCos (H : ℕ) (x : ℝ) :
    ndFejerKernel H x =
      (H + 1 : ℕ) +
        2 * ∑ j ∈ Finset.range H,
          ((H - j : ℕ) : ℝ) *
            Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) := by
  induction H with
  | zero => simp [ndFejerKernel, ndFejerSum, ndCircleChar, Complex.normSq]
  | succ H ih =>
      rw [ndFejerKernel_succ, ih]
      rw [ndWeightedCosSum_succ]
      push_cast
      ring

private theorem intervalIntegral_cos_mul_const (a b : ℝ) (ha : a ≠ 0) :
    (∫ x in (0 : ℝ)..b, Real.cos (a * x)) = Real.sin (a * b) / a := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.sin (a * y) / a) (Real.cos (a * x)) x := by
    intro x
    convert ((Real.hasDerivAt_sin (a * x)).comp x
      (hasDerivAt_const_mul a)).div_const a using 1
    all_goals field_simp [ha]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x)]
  · simp
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

private theorem intervalIntegral_cos_two_pi_nat_one (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..1,
      Real.cos (2 * Real.pi * (n : ℝ) * x)) = 0 := by
  rw [intervalIntegral_cos_mul_const (2 * Real.pi * (n : ℝ)) 1 (by positivity)]
  rw [show 2 * Real.pi * (n : ℝ) * 1 = ((2 * n : ℕ) : ℝ) * Real.pi by
    push_cast
    ring]
  rw [Real.sin_nat_mul_pi]
  simp

private theorem intervalIntegral_cos_two_pi_nat_half (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..(1 / 2 : ℝ),
      Real.cos (2 * Real.pi * (n : ℝ) * x)) = 0 := by
  rw [intervalIntegral_cos_mul_const (2 * Real.pi * (n : ℝ)) (1 / 2) (by positivity)]
  rw [show 2 * Real.pi * (n : ℝ) * (1 / 2) = (n : ℝ) * Real.pi by ring]
  rw [Real.sin_nat_mul_pi]
  simp

/-- The unnormalized Fejer kernel has total mass `H + 1` on one period. -/
theorem intervalIntegral_ndFejerKernel (H : ℕ) :
    (∫ x in (0 : ℝ)..1, ndFejerKernel H x) = (H + 1 : ℕ) := by
  simp_rw [ndFejerKernel_eq_triangularCos]
  have hconst : IntervalIntegrable (fun _ : ℝ => ((H + 1 : ℕ) : ℝ)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hsum : IntervalIntegrable (fun x : ℝ =>
      2 * ∑ j ∈ Finset.range H, ((H - j : ℕ) : ℝ) *
        Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_add hconst hsum]
  simp only [intervalIntegral.integral_const, one_smul, sub_zero,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finset_sum]
  · simp only [intervalIntegral.integral_const_mul]
    have hz :
        (∑ j ∈ Finset.range H, ((H - j : ℕ) : ℝ) *
          (∫ x in (0 : ℝ)..1,
            Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [intervalIntegral_cos_two_pi_nat_one (j + 1) (by omega)]
      simp
    rw [hz]
    ring
  · intro j hj
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Half of a period has exactly half of the Fejer kernel's mass. -/
theorem intervalIntegral_zero_half_ndFejerKernel (H : ℕ) :
    (∫ x in (0 : ℝ)..(1 / 2 : ℝ), ndFejerKernel H x) =
      ((H + 1 : ℕ) : ℝ) / 2 := by
  simp_rw [ndFejerKernel_eq_triangularCos]
  have hconst : IntervalIntegrable (fun _ : ℝ => ((H + 1 : ℕ) : ℝ))
      volume 0 (1 / 2) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hsum : IntervalIntegrable (fun x : ℝ =>
      2 * ∑ j ∈ Finset.range H, ((H - j : ℕ) : ℝ) *
        Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x))
      volume 0 (1 / 2) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_add hconst hsum]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finset_sum]
  · simp only [intervalIntegral.integral_const_mul]
    have hz :
        (∑ j ∈ Finset.range H, ((H - j : ℕ) : ℝ) *
          (∫ x in (0 : ℝ)..(1 / 2 : ℝ),
            Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [intervalIntegral_cos_two_pi_nat_half (j + 1) (by omega)]
      simp
    rw [hz]
    ring
  · intro j hj
    exact Continuous.intervalIntegrable (by fun_prop) _ _

private theorem ndCircleChar_nat_pow (r : ℕ) (x : ℝ) :
    ndCircleChar (r : ℤ) x = ndCircleChar 1 x ^ r := by
  simp only [ndCircleChar, Int.cast_natCast, Int.cast_one, one_mul]
  rw [show (r : ℝ) * x = r • x by simp [nsmul_eq_mul]]
  rw [AddChar.map_nsmul_eq_pow]
  exact Circle.coe_pow _ _

private theorem norm_ndCircleChar_sub_one (h : ℤ) (x : ℝ) :
    ‖ndCircleChar h x - 1‖ =
      2 * |Real.sin (Real.pi * (h : ℝ) * x)| := by
  rw [ndCircleChar, Real.fourierChar_apply]
  rw [show (((2 * Real.pi * ((h : ℝ) * x) : ℝ) : ℂ) * Complex.I) =
      Complex.I * (((2 * Real.pi * ((h : ℝ) * x) : ℝ) : ℂ)) by ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * ((h : ℝ) * x) / 2 =
    Real.pi * (h : ℝ) * x by ring]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]

private theorem ndFejerSum_eq_geom_div (H : ℕ) (x : ℝ)
    (hx : Real.sin (Real.pi * x) ≠ 0) :
    ndFejerSum H x =
      (ndCircleChar (H + 1 : ℕ) x - 1) / (ndCircleChar 1 x - 1) := by
  have hz : ndCircleChar 1 x ≠ 1 := by
    intro hz
    have hzero : ‖ndCircleChar 1 x - 1‖ = 0 := by
      rw [hz, sub_self, norm_zero]
    rw [norm_ndCircleChar_sub_one] at hzero
    norm_num at hzero
    exact hx hzero
  rw [ndFejerSum]
  have hsum :
      (∑ r ∈ Finset.range (H + 1), ndCircleChar (r : ℤ) x) =
        ∑ r ∈ Finset.range (H + 1), ndCircleChar 1 x ^ r := by
    apply Finset.sum_congr rfl
    intro r hr
    exact ndCircleChar_nat_pow r x
  rw [hsum, geom_sum_eq hz]
  congr 2
  exact (ndCircleChar_nat_pow (H + 1) x).symm

/-- Away from integer phases, the Fejer kernel is the exact sine quotient. -/
theorem ndFejerKernel_eq_sin_sq_div (H : ℕ) (x : ℝ)
    (hx : Real.sin (Real.pi * x) ≠ 0) :
    ndFejerKernel H x =
      Real.sin ((H + 1 : ℕ) * Real.pi * x) ^ 2 /
        Real.sin (Real.pi * x) ^ 2 := by
  rw [ndFejerKernel, ndFejerSum_eq_geom_div H x hx, Complex.normSq_div]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [norm_ndCircleChar_sub_one, norm_ndCircleChar_sub_one]
  push_cast
  simp only [mul_pow, sq_abs]
  ring

/-- On the positive half-period, the Fejer kernel has the reciprocal-square bound. -/
theorem ndFejerKernel_le_inv_four_mul_sq
    (H : ℕ) (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    ndFejerKernel H x ≤ 1 / (4 * x ^ 2) := by
  have harg0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx.le
  have harghalf : Real.pi * x ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin harg0 harghalf
  have hsin_lower : 2 * x ≤ Real.sin (Real.pi * x) := by
    convert hjordan using 1
    field_simp [Real.pi_ne_zero]
  have hsinpos : 0 < Real.sin (Real.pi * x) :=
    lt_of_lt_of_le (by positivity) hsin_lower
  have hdensq : 4 * x ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
    nlinarith
  rw [ndFejerKernel_eq_sin_sq_div H x hsinpos.ne']
  have hfirst :
      Real.sin ((H + 1 : ℕ) * Real.pi * x) ^ 2 /
          Real.sin (Real.pi * x) ^ 2 ≤
        1 / Real.sin (Real.pi * x) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hsinpos) (sq_pos_of_pos hsinpos)]
    nlinarith [Real.sin_sq_le_one ((H + 1 : ℕ) * Real.pi * x)]
  exact hfirst.trans (one_div_le_one_div_of_le (by positivity) hdensq)

private theorem one_div_four_mul_sq_eq_zpow (x : ℝ) :
    1 / (4 * x ^ 2) = (1 / 4 : ℝ) * x ^ (-2 : ℤ) := by
  calc
    1 / (4 * x ^ 2) = (1 / 4 : ℝ) * (x ^ 2)⁻¹ := by
      simp only [one_div]
      rw [mul_inv_rev (4 : ℝ) (x ^ 2)]
      ring
    _ = (1 / 4 : ℝ) * x ^ (-2 : ℤ) := by
      simp only [zpow_neg, Int.reduceNeg]
      rfl

private theorem intervalIntegral_one_div_four_sq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, 1 / (4 * x ^ 2)) =
      1 / (4 * a) - 1 / (4 * b) := by
  rw [show (fun x : ℝ => 1 / (4 * x ^ 2)) =
      fun x : ℝ => (1 / 4 : ℝ) * x ^ (-2 : ℤ) by
    funext x
    exact one_div_four_mul_sq_eq_zpow x]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_zpow (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt ha hb⟩)]
  norm_num [zpow_neg_one]
  field_simp [ha.ne', hb.ne']
  ring

/-- The exact integrated reciprocal-square tail, together with its coarser bound. -/
theorem intervalIntegral_ndFejerKernel_tail_le
    (H : ℕ) (D : ℝ) (hD : 0 < D) (hD1 : D ≤ 1) :
    (∫ x in D / 2..(1 / 2 : ℝ), ndFejerKernel H x) ≤
        1 / (2 * D) - 1 / 2 ∧
      1 / (2 * D) - 1 / 2 ≤ 1 / (2 * D) := by
  have ha : 0 < D / 2 := by positivity
  have hb : 0 < (1 / 2 : ℝ) := by norm_num
  have hab : D / 2 ≤ (1 / 2 : ℝ) := by nlinarith
  have hKint : IntervalIntegrable (ndFejerKernel H) volume (D / 2) (1 / 2) :=
    (continuous_ndFejerKernel H).intervalIntegrable _ _
  have hzero : (0 : ℝ) ∉ Set.uIcc (D / 2) (1 / 2) :=
    Set.notMem_uIcc_of_lt ha hb
  have hgint : IntervalIntegrable (fun x : ℝ => 1 / (4 * x ^ 2))
      volume (D / 2) (1 / 2) := by
    rw [show (fun x : ℝ => 1 / (4 * x ^ 2)) =
        fun x : ℝ => (1 / 4 : ℝ) * x ^ (-2 : ℤ) by
      funext x
      exact one_div_four_mul_sq_eq_zpow x]
    exact (intervalIntegral.intervalIntegrable_zpow (μ := volume)
      (n := (-2 : ℤ)) (Or.inr hzero)).const_mul (1 / 4)
  constructor
  · calc
      (∫ x in D / 2..(1 / 2 : ℝ), ndFejerKernel H x)
          ≤ ∫ x in D / 2..(1 / 2 : ℝ), 1 / (4 * x ^ 2) := by
            exact intervalIntegral.integral_mono_on hab hKint hgint
              (fun x hx => ndFejerKernel_le_inv_four_mul_sq H x
                (lt_of_lt_of_le ha hx.1) hx.2)
      _ = 1 / (2 * D) - 1 / 2 := by
            rw [intervalIntegral_one_div_four_sq ha hb]
            field_simp [hD.ne']
            ring
  · linarith

end ND
end Erdos1135
