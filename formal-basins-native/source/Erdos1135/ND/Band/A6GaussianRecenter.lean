import Erdos1135.ND.Band.A6Gaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A6 Neutral Gaussian Recentering

This neutral leaf compares two centered Gaussian scales without importing the
negative-binomial local law or the physical A5 geometry.  Its multiplicative
upper bound is shaped for the later pointwise physical consumer, where it
avoids replacing a local relative error by a premature factor three.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Exact logarithmic exponent relating Gaussian scales `N` and `S`. -/
def ndA6GaussianRecenterExponent (N S x : ℝ) : ℝ :=
  (Real.log S - Real.log N) / 2 + x ^ 2 * (N - S) / (4 * N * S)

/-- Explicit relative scale-change budget used by the A6 recentering step. -/
def ndA6GaussianRecenterZeta (N S x : ℝ) : ℝ :=
  (3 / 4) * |N - S| / S +
    (3 / 8) * x ^ 2 * |N - S| / S ^ 2

/-- The explicit recentering budget is nonnegative at positive target scale. -/
theorem ndA6GaussianRecenterZeta_nonneg
    {N S x : ℝ} (hS : 0 < S) :
    0 ≤ ndA6GaussianRecenterZeta N S x := by
  unfold ndA6GaussianRecenterZeta
  positivity

/-- The Gaussian scale change is exactly multiplication by the recentering
exponential.  The signs in both logarithmic and quadratic terms are fixed by
this identity. -/
theorem ndA6Gaussian_eq_mul_exp_recenterExponent
    {N S x : ℝ} (hN : 0 < N) (hS : 0 < S) :
    ndA6Gaussian N x =
      ndA6Gaussian S x * Real.exp (ndA6GaussianRecenterExponent N S x) := by
  have hExpLog :
      Real.exp ((Real.log S - Real.log N) / 2) = Real.sqrt (S / N) := by
    rw [← Real.log_div hS.ne' hN.ne', Real.exp_half,
      Real.exp_log (div_pos hS hN)]
  have hRadicand :
      4 * Real.pi * S = (4 * Real.pi * N) * (S / N) := by
    field_simp [hN.ne']
  have hSqrt :
      Real.sqrt (4 * Real.pi * S) =
        Real.sqrt (4 * Real.pi * N) * Real.sqrt (S / N) := by
    rw [hRadicand, Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi * N)]
  have hNorm :
      (Real.sqrt (4 * Real.pi * N))⁻¹ =
        (Real.sqrt (4 * Real.pi * S))⁻¹ *
          Real.exp ((Real.log S - Real.log N) / 2) := by
    rw [hExpLog, hSqrt]
    have hNroot : Real.sqrt (4 * Real.pi * N) ≠ 0 := by positivity
    have hRatioRoot : Real.sqrt (S / N) ≠ 0 := by positivity
    field_simp [hNroot, hRatioRoot]
  have hQuadratic :
      -(x ^ 2 / (4 * N)) =
        -(x ^ 2 / (4 * S)) + x ^ 2 * (N - S) / (4 * N * S) := by
    field_simp [hN.ne', hS.ne']
    ring
  unfold ndA6Gaussian ndA6GaussianRecenterExponent
  calc
    (Real.sqrt (4 * Real.pi * N))⁻¹ *
        Real.exp (-(x ^ 2 / (4 * N))) =
        ((Real.sqrt (4 * Real.pi * S))⁻¹ *
          Real.exp ((Real.log S - Real.log N) / 2)) *
            Real.exp (-(x ^ 2 / (4 * N))) := by rw [hNorm]
    _ = (Real.sqrt (4 * Real.pi * S))⁻¹ *
          Real.exp (-(x ^ 2 / (4 * S))) *
            Real.exp
              ((Real.log S - Real.log N) / 2 +
                x ^ 2 * (N - S) / (4 * N * S)) := by
      rw [hQuadratic, Real.exp_add, Real.exp_add]
      ring

private theorem abs_log_sub_log_le_recenter
    {N S : ℝ} (hN : 0 < N) (hS : 0 < S)
    (hclose : |N - S| ≤ S / 3) :
    |Real.log S - Real.log N| ≤ (3 / 2) * |N - S| / S := by
  have hNlower : 2 * S ≤ 3 * N := by
    rw [abs_le] at hclose
    nlinarith
  rcases le_total N S with hNS | hSN
  · have hlogNonneg : 0 ≤ Real.log S - Real.log N := by
      exact sub_nonneg.mpr (Real.log_le_log hN hNS)
    rw [abs_of_nonneg hlogNonneg, abs_of_nonpos (sub_nonpos.mpr hNS)]
    rw [← Real.log_div hS.ne' hN.ne']
    have hInv : 1 / N ≤ 3 / (2 * S) := by
      apply (div_le_div_iff₀ hN (by positivity : 0 < 2 * S)).2
      simpa using hNlower
    calc
      Real.log (S / N) ≤ S / N - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hS hN)
      _ = (S - N) * (1 / N) := by field_simp [hN.ne']
      _ ≤ (S - N) * (3 / (2 * S)) :=
        mul_le_mul_of_nonneg_left hInv (sub_nonneg.mpr hNS)
      _ = (3 / 2) * (S - N) / S := by ring
      _ = (3 / 2) * -(N - S) / S := by ring
  · have hlogNonpos : Real.log S - Real.log N ≤ 0 := by
      exact sub_nonpos.mpr (Real.log_le_log hS hSN)
    rw [abs_of_nonpos hlogNonpos, abs_of_nonneg (sub_nonneg.mpr hSN)]
    rw [show -(Real.log S - Real.log N) =
        Real.log N - Real.log S by ring,
      ← Real.log_div hN.ne' hS.ne']
    calc
      Real.log (N / S) ≤ N / S - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hN hS)
      _ = (N - S) / S := by field_simp [hS.ne']
      _ ≤ (3 / 2) * ((N - S) / S) :=
        le_mul_of_one_le_left
          (div_nonneg (sub_nonneg.mpr hSN) hS.le) (by norm_num)
      _ = (3 / 2) * (N - S) / S := by ring

/-- A relative scale displacement of at most one third controls the exact
Gaussian recentering exponent by the explicit zeta budget. -/
theorem abs_ndA6GaussianRecenterExponent_le_zeta
    {N S x : ℝ} (hN : 0 < N) (hS : 0 < S)
    (hclose : |N - S| ≤ S / 3) :
    |ndA6GaussianRecenterExponent N S x| ≤
      ndA6GaussianRecenterZeta N S x := by
  have hNlower : 2 * S ≤ 3 * N := by
    rw [abs_le] at hclose
    nlinarith
  have hlog := abs_log_sub_log_le_recenter hN hS hclose
  have hlogHalf :
      |(Real.log S - Real.log N) / 2| ≤
        (3 / 4) * |N - S| / S := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |Real.log S - Real.log N| / 2 ≤
          ((3 / 2) * |N - S| / S) / 2 :=
        div_le_div_of_nonneg_right hlog (by norm_num)
      _ = (3 / 4) * |N - S| / S := by ring
  have hInv : 1 / (4 * N * S) ≤ 3 / (8 * S ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * N * S)
      (by positivity : 0 < 8 * S ^ 2)).2
    have hscaled := mul_le_mul_of_nonneg_left hNlower
      (show 0 ≤ 4 * S by positivity)
    nlinarith
  have hQuadraticAbs :
      |x ^ 2 * (N - S) / (4 * N * S)| =
        x ^ 2 * |N - S| / (4 * N * S) := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_pos (by positivity : 0 < 4 * N * S)]
  have hQuadratic :
      |x ^ 2 * (N - S) / (4 * N * S)| ≤
        (3 / 8) * x ^ 2 * |N - S| / S ^ 2 := by
    rw [hQuadraticAbs]
    calc
      x ^ 2 * |N - S| / (4 * N * S) =
          (x ^ 2 * |N - S|) * (1 / (4 * N * S)) := by ring
      _ ≤ (x ^ 2 * |N - S|) * (3 / (8 * S ^ 2)) :=
        mul_le_mul_of_nonneg_left hInv
          (mul_nonneg (sq_nonneg x) (abs_nonneg _))
      _ = (3 / 8) * x ^ 2 * |N - S| / S ^ 2 := by ring
  unfold ndA6GaussianRecenterExponent ndA6GaussianRecenterZeta
  exact (abs_add_le _ _).trans (add_le_add hlogHalf hQuadratic)

/-- Under a unit zeta budget, changing Gaussian scale costs at most twice
zeta relative to the target Gaussian. -/
theorem abs_ndA6Gaussian_sub_le_two_mul_recenterZeta
    {N S x : ℝ} (hN : 0 < N) (hS : 0 < S)
    (hclose : |N - S| ≤ S / 3)
    (hzeta : ndA6GaussianRecenterZeta N S x ≤ 1) :
    |ndA6Gaussian N x - ndA6Gaussian S x| ≤
      ndA6Gaussian S x * (2 * ndA6GaussianRecenterZeta N S x) := by
  let e := ndA6GaussianRecenterExponent N S x
  let zeta := ndA6GaussianRecenterZeta N S x
  have he : |e| ≤ zeta := by
    simpa [e, zeta] using
      abs_ndA6GaussianRecenterExponent_le_zeta hN hS hclose
  have heOne : |e| ≤ 1 := he.trans (by simpa [zeta] using hzeta)
  have hExp : |Real.exp e - 1| ≤ 2 * zeta :=
    (Real.abs_exp_sub_one_le heOne).trans
      (mul_le_mul_of_nonneg_left he (by norm_num))
  rw [ndA6Gaussian_eq_mul_exp_recenterExponent hN hS]
  change
    |ndA6Gaussian S x * Real.exp e - ndA6Gaussian S x| ≤ _
  rw [show ndA6Gaussian S x * Real.exp e - ndA6Gaussian S x =
      ndA6Gaussian S x * (Real.exp e - 1) by ring]
  rw [abs_mul, abs_of_nonneg (ndA6Gaussian_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left hExp (ndA6Gaussian_nonneg _ _)

/-- Consumer-shaped upper comparison retaining the sharp multiplicative
factor `1 + 2*zeta`. -/
theorem ndA6Gaussian_le_one_add_two_mul_recenterZeta
    {N S x : ℝ} (hN : 0 < N) (hS : 0 < S)
    (hclose : |N - S| ≤ S / 3)
    (hzeta : ndA6GaussianRecenterZeta N S x ≤ 1) :
    ndA6Gaussian N x ≤
      ndA6Gaussian S x * (1 + 2 * ndA6GaussianRecenterZeta N S x) := by
  have hdiff := abs_ndA6Gaussian_sub_le_two_mul_recenterZeta
    hN hS hclose hzeta
  have hle : ndA6Gaussian N x - ndA6Gaussian S x ≤
      ndA6Gaussian S x * (2 * ndA6GaussianRecenterZeta N S x) :=
    (le_abs_self _).trans hdiff
  linarith

/-- Coarser factor-three corollary for consumers that no longer need the
sharp multiplicative zeta factor. -/
theorem ndA6Gaussian_le_three_mul_of_recenter
    {N S x : ℝ} (hN : 0 < N) (hS : 0 < S)
    (hclose : |N - S| ≤ S / 3)
    (hzeta : ndA6GaussianRecenterZeta N S x ≤ 1) :
    ndA6Gaussian N x ≤ 3 * ndA6Gaussian S x := by
  have hmain := ndA6Gaussian_le_one_add_two_mul_recenterZeta
    hN hS hclose hzeta
  have hzetaNonneg := ndA6GaussianRecenterZeta_nonneg (N := N) (x := x) hS
  have hfactor : 1 + 2 * ndA6GaussianRecenterZeta N S x ≤ 3 := by
    linarith
  exact hmain.trans (by
    have hphi := ndA6Gaussian_nonneg S x
    nlinarith)

section Canaries

example (S x : ℝ) : ndA6GaussianRecenterExponent S S x = 0 := by
  simp [ndA6GaussianRecenterExponent]

example (S x : ℝ) :
    ndA6GaussianRecenterZeta S S x = 0 := by
  simp [ndA6GaussianRecenterZeta]

example : ndA6GaussianRecenterZeta 2 3 1 = 7 / 24 := by
  norm_num [ndA6GaussianRecenterZeta, abs_of_nonpos]

example : ndA6GaussianRecenterZeta 4 3 0 = 1 / 4 := by
  norm_num [ndA6GaussianRecenterZeta, abs_of_nonneg]

end Canaries

end


end ND
end Erdos1135
