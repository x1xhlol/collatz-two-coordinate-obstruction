/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageSignedTotal
import Erdos1135SecondScale.Tao.Renewal.SeparatedWindowFlattening

/-!
# Signed Sparse Center Sum

This leaf combines the checked two-kernel local average, countable disjoint
window flattening, and signed all-integer total mass into the source-shaped
`1/d` sparse-center estimate.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped BigOperators

namespace TaoSection7Lemma77

/-- The rate-`c/2` kernel summed over `d`-separated integer centers is
controlled by the explicit rate-`c/4` total with the expected `1/d` gain. -/
theorem lemma77SignedTranslatedHorizontalKernel_tsum_separated_centers_le
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (shift : ℤ) (s d : ℕ) (centers : Set ℤ)
    (hd : 0 < d)
    (hd2 : (d : ℝ) ^ 2 ≤ 1 + (s : ℝ))
    (hsep : centers.Pairwise
      (fun c₁ c₂ => (d : ℤ) ≤ |c₁ - c₂|)) :
    (∑' center : centers,
      lemma77SignedTranslatedHorizontalKernel
        C (c / 2) shift s center.1) ≤
      (2 * Real.exp ((c / 2) ^ 2) / (d : ℝ)) *
        (C *
          (lemma77HorizontalGaussianCountConstant ((c / 4) ^ 2) +
            lemma77HorizontalLinearCountConstant (c / 4))) := by
  let K : ℤ → ℝ := fun z =>
    lemma77SignedTranslatedHorizontalKernel C (c / 4) shift s z
  let A : ℝ := 2 * Real.exp ((c / 2) ^ 2) / (d : ℝ)
  have hc2 : 0 < c / 2 := by positivity
  have hc4 : 0 < c / 4 := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hK0 : ∀ z, 0 ≤ K z := by
    intro z
    exact lemma77SignedTranslatedHorizontalKernel_nonneg hC shift s z
  have hK : Summable K := by
    simpa [K] using
      lemma77SignedTranslatedHorizontalKernel_summable
        (C := C) hc4 shift s
  have hwindow0 : ∀ center : centers,
      0 ≤ (taoSection7CenteredHalfOpenIntWindow d center.1).sum K := by
    intro center
    exact Finset.sum_nonneg fun z _ => hK0 z
  have hwindow : Summable fun center : centers =>
      (taoSection7CenteredHalfOpenIntWindow d center.1).sum K := by
    refine summable_of_sum_le (c := ∑' z : ℤ, K z) hwindow0 ?_
    intro u
    have hdisj :
        ((u : Set centers)).PairwiseDisjoint
          (fun center =>
            taoSection7CenteredHalfOpenIntWindow d center.1) := by
      intro i _hi j _hj hij
      apply taoSection7CenteredHalfOpenIntWindow_disjoint_of_width_le_abs_sub
      exact hsep i.2 j.2 (fun h => hij (Subtype.ext h))
    have hu :=
      taoSection7_tsum_finset_sum_le_tsum_of_pairwiseDisjoint
        (u : Set centers)
        (fun center : centers =>
          taoSection7CenteredHalfOpenIntWindow d center.1)
        K hdisj hK0 hK
    have heq :
        (∑' i : (u : Set centers),
          (taoSection7CenteredHalfOpenIntWindow d i.1.1).sum K) =
          u.sum (fun i =>
            (taoSection7CenteredHalfOpenIntWindow d i.1).sum K) := by
      rw [tsum_fintype, ← Finset.attach_eq_univ]
      exact Finset.sum_attach u
        (fun i : centers =>
          (taoSection7CenteredHalfOpenIntWindow d i.1).sum K)
    simpa only [heq] using hu
  have hleft : Summable fun center : centers =>
      lemma77SignedTranslatedHorizontalKernel
        C (c / 2) shift s center.1 := by
    simpa only [Function.comp_apply] using
      (lemma77SignedTranslatedHorizontalKernel_summable
        (C := C) hc2 shift s).comp_injective Subtype.val_injective
  have hright : Summable fun center : centers =>
      A * (taoSection7CenteredHalfOpenIntWindow d center.1).sum K :=
    hwindow.mul_left A
  have hpoint (center : centers) :
      lemma77SignedTranslatedHorizontalKernel
          C (c / 2) shift s center.1 ≤
        A * (taoSection7CenteredHalfOpenIntWindow d center.1).sum K := by
    simpa [A, K] using
      lemma77SignedTranslatedHorizontalKernel_centeredHalfOpen_localAverage_le
        hC hc shift s d center.1 hd hd2
  have havg := hleft.tsum_le_tsum hpoint hright
  have hflat :=
    taoSection7_tsum_centeredHalfOpenIntWindow_le_tsum
      centers d K hsep hK0 hK
  have htotal :
      (∑' z : ℤ, K z) ≤
        C * (lemma77HorizontalGaussianCountConstant ((c / 4) ^ 2) +
          lemma77HorizontalLinearCountConstant (c / 4)) := by
    simpa [K] using
      lemma77SignedTranslatedHorizontalKernel_tsum_le
        hC hc4 shift s
  calc
    _ ≤ ∑' center : centers,
        A * (taoSection7CenteredHalfOpenIntWindow d center.1).sum K := havg
    _ = A * ∑' center : centers,
        (taoSection7CenteredHalfOpenIntWindow d center.1).sum K := by
      rw [tsum_mul_left]
    _ ≤ A * ∑' z : ℤ, K z := mul_le_mul_of_nonneg_left hflat hA
    _ ≤ _ := by
      simpa [A] using mul_le_mul_of_nonneg_left htotal hA

end TaoSection7Lemma77

end
end Tao
end Erdos1135SecondScale
