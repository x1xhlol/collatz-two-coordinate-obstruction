/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageTails

/-!
# Signed Sparse Horizontal Kernel

This leaf develops the translation-uniform signed kernel estimates needed for
the separated-window proof of Tao's `(7.62)`.  The first comparison weakens
the rate from `c` to `c / 2` across a displacement no larger than the kernel
width.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- The signed height kernel translated by an arbitrary integer shift. -/
def lemma77SignedTranslatedHorizontalKernel
    (C c : ℝ) (shift : ℤ) (s : ℕ) (z : ℤ) : ℝ :=
  lemma77HeightPotentialKernel C c (z - shift) s

/-- A translated signed height kernel is nonnegative when its leading
constant is nonnegative. -/
theorem lemma77SignedTranslatedHorizontalKernel_nonneg
    {C c : ℝ} (hC : 0 ≤ C) (shift : ℤ) (s : ℕ) (z : ℤ) :
    0 ≤ lemma77SignedTranslatedHorizontalKernel C c shift s z :=
  lemma77HeightPotentialKernel_nonneg hC (z - shift) s

/-- Tao's two-term Gaussian weight is even. -/
@[simp] theorem taoLemma22GaussianWeight_neg (n : ℕ) (x : ℝ) :
    taoLemma22GaussianWeight n (-x) = taoLemma22GaussianWeight n x := by
  unfold taoLemma22GaussianWeight
  split <;> simp

/-- Across a displacement within the Gaussian width, the two-term Gaussian
weight at rate `c` is controlled by the rate-`c/2` weight.  The near branch
uses the Gaussian term; the far branch uses radial monotonicity of both terms. -/
theorem taoLemma22GaussianWeight_bounded_int_shift_le
    {c : ℝ} (hc : 0 < c) (s : ℕ) {z w : ℤ}
    (hshift : (((z - w : ℤ) : ℝ) ^ 2 ≤ 1 + (s : ℝ))) :
    taoLemma22GaussianWeight (1 + s)
        (c * lemma77ScalarCenteredHorizontal z s) ≤
      2 * Real.exp (c ^ 2) *
        taoLemma22GaussianWeight (1 + s)
          ((c / 2) * lemma77ScalarCenteredHorizontal w s) := by
  let x := lemma77ScalarCenteredHorizontal z s
  let y := lemma77ScalarCenteredHorizontal w s
  let S : ℝ := ((1 + s : ℕ) : ℝ)
  have hS : 0 < S := by positivity
  have hxy : (x - y) ^ 2 ≤ S := by
    rw [Int.cast_sub] at hshift
    dsimp [x, y, S, lemma77ScalarCenteredHorizontal]
    push_cast
    nlinarith [hshift]
  change taoLemma22GaussianWeight (1 + s) (c * x) ≤
    2 * Real.exp (c ^ 2) *
      taoLemma22GaussianWeight (1 + s) ((c / 2) * y)
  by_cases hnear : y ^ 2 ≤ 4 * S
  · have hm := mul_le_mul_of_nonneg_left hnear (sq_nonneg c)
    have hnum : ((c / 2) * y) ^ 2 ≤ c ^ 2 * S := by
      nlinarith [hm]
    have hq : ((c / 2) * y) ^ 2 / S ≤ c ^ 2 :=
      (div_le_iff₀ hS).2 hnum
    have hexp :
        Real.exp (-(c ^ 2)) ≤
          Real.exp (-(((c / 2) * y) ^ 2 / S)) := by
      rw [Real.exp_le_exp]
      linarith
    have hweak :
        Real.exp (-(c ^ 2)) ≤
          taoLemma22GaussianWeight (1 + s) ((c / 2) * y) := by
      rw [taoLemma22GaussianWeight, if_neg (by omega)]
      exact le_trans (by simpa [S] using hexp)
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    have hcoef : 0 ≤ 2 * Real.exp (c ^ 2) := by positivity
    have hscale := mul_le_mul_of_nonneg_left hweak hcoef
    have hcancel :
        (2 * Real.exp (c ^ 2)) * Real.exp (-(c ^ 2)) = 2 := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    calc
      taoLemma22GaussianWeight (1 + s) (c * x) ≤ 2 :=
        taoLemma22GaussianWeight_le_two _ _
      _ = (2 * Real.exp (c ^ 2)) * Real.exp (-(c ^ 2)) := hcancel.symm
      _ ≤ _ := hscale
  · have hfar : 4 * S ≤ y ^ 2 := (lt_of_not_ge hnear).le
    have hfour : (2 * (x - y)) ^ 2 ≤ y ^ 2 := by
      nlinarith [hxy, hfar]
    have hd : 2 * |x - y| ≤ |y| := by
      have hsquares := sq_le_sq.mp hfour
      simpa [abs_mul] using hsquares
    have htail :
        taoLemma22GaussianWeight (1 + s) (c * x) ≤
          taoLemma22GaussianWeight (1 + s) ((c / 2) * y) := by
      rcases le_total x y with hxy' | hyx'
      · have hsmall : y - x ≤ |y| / 2 := by
          rw [abs_of_nonpos (sub_nonpos.mpr hxy')] at hd
          nlinarith
        have h := lemma77HorizontalConvolution732_weight_smallShift_le
          (c := c) (ch := c / 2) (x := y) (n := y - x)
          hc (half_pos hc) (by linarith)
          (sub_nonneg.mpr hxy') hsmall s
        convert h using 1
        all_goals ring_nf
      · have hd' : 2 * |x - y| ≤ |-y| := by simpa using hd
        have hsmall : x - y ≤ |-y| / 2 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hyx')] at hd'
          nlinarith
        have h := lemma77HorizontalConvolution732_weight_smallShift_le
          (c := c) (ch := c / 2) (x := -y) (n := x - y)
          hc (half_pos hc) (by linarith)
          (sub_nonneg.mpr hyx') hsmall s
        calc
          taoLemma22GaussianWeight (1 + s) (c * x) =
              taoLemma22GaussianWeight (1 + s) (c * (-x)) := by
                rw [show c * (-x) = -(c * x) by ring,
                  taoLemma22GaussianWeight_neg]
          _ = taoLemma22GaussianWeight (1 + s)
              (c * (-y - (x - y))) := by
                congr 2
                ring
          _ ≤ taoLemma22GaussianWeight (1 + s) ((c / 2) * (-y)) := h
          _ = taoLemma22GaussianWeight (1 + s) ((c / 2) * y) := by
                rw [show (c / 2) * (-y) = -((c / 2) * y) by ring,
                  taoLemma22GaussianWeight_neg]
    have hone : 1 ≤ 2 * Real.exp (c ^ 2) := by
      nlinarith [Real.one_le_exp (sq_nonneg c)]
    exact htail.trans (by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hone
          (taoLemma22GaussianWeight_nonneg (1 + s) ((c / 2) * y))))

/-- Kernel-level form of bounded-shift rate weakening. -/
theorem lemma77HeightPotentialKernel_bounded_int_shift_le
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (s : ℕ) {z w : ℤ}
    (hshift : (((z - w : ℤ) : ℝ) ^ 2 ≤ 1 + (s : ℝ))) :
    lemma77HeightPotentialKernel C c z s ≤
      2 * Real.exp (c ^ 2) *
        lemma77HeightPotentialKernel C (c / 2) w s := by
  have hweight := taoLemma22GaussianWeight_bounded_int_shift_le
    hc s hshift
  have hfactor :
      0 ≤ C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
    exact mul_nonneg hC (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hweight hfactor
  calc
    lemma77HeightPotentialKernel C c z s ≤
        (C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ)))) *
          (2 * Real.exp (c ^ 2) *
            taoLemma22GaussianWeight (1 + s)
              ((c / 2) * lemma77ScalarCenteredHorizontal w s)) := by
                simpa [lemma77HeightPotentialKernel,
                  lemma77ScalarCenteredHorizontal] using hmul
    _ = 2 * Real.exp (c ^ 2) *
        lemma77HeightPotentialKernel C (c / 2) w s := by
          unfold lemma77HeightPotentialKernel
          rw [show (c / 2) * ((w : ℝ) - (s : ℝ) / 4) =
            (c / 2) * lemma77ScalarCenteredHorizontal w s by rfl]
          ring

/-- Translation-uniform bounded-shift comparison for the signed kernel. -/
theorem lemma77SignedTranslatedHorizontalKernel_bounded_shift_le
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (shift : ℤ) (s : ℕ) {z w : ℤ}
    (hshift : (((z - w : ℤ) : ℝ) ^ 2 ≤ 1 + (s : ℝ))) :
    lemma77SignedTranslatedHorizontalKernel C c shift s z ≤
      2 * Real.exp (c ^ 2) *
        lemma77SignedTranslatedHorizontalKernel C (c / 2) shift s w := by
  apply lemma77HeightPotentialKernel_bounded_int_shift_le hC hc
  have hdiff : (z - shift) - (w - shift) = z - w := by ring
  simpa only [hdiff] using hshift

/-- Radius-form bounded-shift comparison.  This is the form used for every
point in a near window of radius `R`. -/
theorem lemma77SignedTranslatedHorizontalKernel_bounded_radius_le
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (shift : ℤ) (s R : ℕ) {z w : ℤ}
    (hzw : |z - w| ≤ (R : ℤ))
    (hR : (R : ℝ) ^ 2 ≤ 1 + (s : ℝ)) :
    lemma77SignedTranslatedHorizontalKernel C c shift s z ≤
      2 * Real.exp (c ^ 2) *
        lemma77SignedTranslatedHorizontalKernel C (c / 2) shift s w := by
  apply lemma77SignedTranslatedHorizontalKernel_bounded_shift_le
    hC hc shift s
  have hcast : |(((z - w : ℤ) : ℝ))| ≤ (R : ℝ) := by
    exact_mod_cast hzw
  have hsquare : (((z - w : ℤ) : ℝ) ^ 2) ≤ (R : ℝ) ^ 2 := by
    have hproduct :
        0 ≤ ((R : ℝ) - |(((z - w : ℤ) : ℝ))|) *
          ((R : ℝ) + |(((z - w : ℤ) : ℝ))|) :=
      mul_nonneg (sub_nonneg.mpr hcast)
        (add_nonneg (by positivity) (abs_nonneg _))
    nlinarith [sq_abs (((z - w : ℤ) : ℝ))]
  exact hsquare.trans hR

end TaoSection7Lemma77

end
end Tao
end Erdos1135SecondScale
