/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageSignedSparse
import Erdos1135SecondScale.Tao.Renewal.SeparatedWindowGeometry

/-!
# Signed Horizontal Kernel Local Average

This leaf proves the second rate weakening in the sparse-kernel route.  A
rate-`c/2` center is controlled by the exact length-`d` average of the
rate-`c/4` kernel under the required kernel-width premise.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped BigOperators

namespace TaoSection7Lemma77

/-- Exact-length local averaging weakens the signed translated kernel rate
from `c/2` to `c/4`. -/
theorem
    lemma77SignedTranslatedHorizontalKernel_centeredHalfOpen_localAverage_le
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (shift : ℤ) (s d : ℕ) (center : ℤ)
    (hd : 0 < d)
    (hd2 : (d : ℝ) ^ 2 ≤ 1 + (s : ℝ)) :
    lemma77SignedTranslatedHorizontalKernel C (c / 2) shift s center ≤
      (2 * Real.exp ((c / 2) ^ 2) / (d : ℝ)) *
        (taoSection7CenteredHalfOpenIntWindow d center).sum
          (fun w =>
            lemma77SignedTranslatedHorizontalKernel
              C (c / 4) shift s w) := by
  have hpoint :
      ∀ w ∈ taoSection7CenteredHalfOpenIntWindow d center,
        lemma77SignedTranslatedHorizontalKernel
            C (c / 2) shift s center ≤
          2 * Real.exp ((c / 2) ^ 2) *
            lemma77SignedTranslatedHorizontalKernel
              C (c / 4) shift s w := by
    intro w hw
    have hrate : (c / 2) / 2 = c / 4 := by ring
    simpa only [hrate] using
      lemma77SignedTranslatedHorizontalKernel_bounded_radius_le
        (c := c / 2) hC (half_pos hc) shift s d
        (z := center) (w := w)
        (abs_sub_center_le_of_mem_taoSection7CenteredHalfOpenIntWindow hw)
        hd2
  have hsum :
      (d : ℝ) *
          lemma77SignedTranslatedHorizontalKernel
            C (c / 2) shift s center ≤
        2 * Real.exp ((c / 2) ^ 2) *
          (taoSection7CenteredHalfOpenIntWindow d center).sum
            (fun w =>
              lemma77SignedTranslatedHorizontalKernel
                C (c / 4) shift s w) := by
    calc
      (d : ℝ) *
          lemma77SignedTranslatedHorizontalKernel
            C (c / 2) shift s center =
          (taoSection7CenteredHalfOpenIntWindow d center).sum
            (fun _ =>
              lemma77SignedTranslatedHorizontalKernel
                C (c / 2) shift s center) := by
        rw [Finset.sum_const,
          card_taoSection7CenteredHalfOpenIntWindow, nsmul_eq_mul]
      _ ≤
          (taoSection7CenteredHalfOpenIntWindow d center).sum
            (fun w =>
              2 * Real.exp ((c / 2) ^ 2) *
                lemma77SignedTranslatedHorizontalKernel
                  C (c / 4) shift s w) :=
        Finset.sum_le_sum hpoint
      _ =
          2 * Real.exp ((c / 2) ^ 2) *
            (taoSection7CenteredHalfOpenIntWindow d center).sum
              (fun w =>
                lemma77SignedTranslatedHorizontalKernel
                  C (c / 4) shift s w) := by
        rw [Finset.mul_sum]
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast hd
  calc
    lemma77SignedTranslatedHorizontalKernel C (c / 2) shift s center ≤
        (2 * Real.exp ((c / 2) ^ 2) *
          (taoSection7CenteredHalfOpenIntWindow d center).sum
            (fun w =>
              lemma77SignedTranslatedHorizontalKernel
                C (c / 4) shift s w)) / (d : ℝ) := by
      apply (le_div_iff₀ hdR).2
      simpa [mul_comm] using hsum
    _ =
        (2 * Real.exp ((c / 2) ^ 2) / (d : ℝ)) *
          (taoSection7CenteredHalfOpenIntWindow d center).sum
            (fun w =>
              lemma77SignedTranslatedHorizontalKernel
                C (c / 4) shift s w) := by
      ring

end TaoSection7Lemma77

end
end Tao
end Erdos1135SecondScale
