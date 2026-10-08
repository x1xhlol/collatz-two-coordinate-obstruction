/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeWindow
import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageHorizontal
import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageSignedSparse
import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageSignedTotal

/-!
# Canonical Outside-Eprime Horizontal Mass

This analytic proof leaf closes the fixed-fresh horizontal-event estimate.
It combines the canonical pointwise first-passage kernel, one radius rate
weakening, exact finite-window overcounting, and the checked countable sparse
sum over `Sigma` centers.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped BigOperators
open TaoSection7Lemma77
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The real center-mass constant after the radius comparison and the sparse
`Sigma` sum.  The separate factor `2 * R + 1` remains outside this quantity. -/
noncomputable def lemma79NearSigmaHorizontalCenterMassBound
    (C32 c32 sMin : ℝ) : ℝ :=
  (2 * Real.exp (c32 ^ 2)) *
    ((2 * Real.exp ((c32 / 2) ^ 2) /
        (Nat.floor (sigmaSeparationScale sMin) : ℝ)) *
      ((300 * C32) *
        (lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) +
          lemma77HorizontalLinearCountConstant (c32 / 4))))

/-- A canonical horizontal atom lying in one translated radius window is
bounded by the weakened signed kernel at that window's center. -/
theorem lemma79CanonicalFirstPassageHorizontalPMF_windowAtom_le_signedCenter
    {C32 c32 : ℝ}
    (hC32 : 0 ≤ C32) (hc32 : 0 < c32)
    (hcanonical :
      ∀ (start : TaoSection7RenewalPoint) (s r : ℕ),
        lemma77CanonicalFirstPassageHorizontalPMF start s r ≤
          ENNReal.ofReal
            (lemma77HorizontalPointwiseKernel
              (c32 ^ 2) c32 (300 * C32) s r))
    (entry : TaoSection7RenewalPoint) (fpGap R : ℕ)
    (shift center : ℤ) (r : ℕ)
    (hR : (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ))
    (hr : (r : ℤ) + shift ∈ taoSection7IntIccWindow R center) :
    lemma77CanonicalFirstPassageHorizontalPMF entry fpGap r ≤
      ENNReal.ofReal
        (2 * Real.exp (c32 ^ 2) *
          lemma77SignedTranslatedHorizontalKernel
            (300 * C32) (c32 / 2) shift fpGap center) := by
  rcases mem_taoSection7IntIccWindow.mp hr with
    ⟨hzLower, hzUpper⟩
  have hzw : |((r : ℤ) + shift) - center| ≤ (R : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hC300 : 0 ≤ 300 * C32 :=
    mul_nonneg (by norm_num) hC32
  have hkernel :
      lemma77SignedTranslatedHorizontalKernel
          (300 * C32) c32 shift fpGap ((r : ℤ) + shift) ≤
        2 * Real.exp (c32 ^ 2) *
          lemma77SignedTranslatedHorizontalKernel
            (300 * C32) (c32 / 2) shift fpGap center :=
    lemma77SignedTranslatedHorizontalKernel_bounded_radius_le
      (C := 300 * C32) (c := c32) hC300 hc32
      shift fpGap R hzw hR
  calc
    lemma77CanonicalFirstPassageHorizontalPMF entry fpGap r ≤
        ENNReal.ofReal
          (lemma77HorizontalPointwiseKernel
            (c32 ^ 2) c32 (300 * C32) fpGap r) :=
      hcanonical entry fpGap r
    _ = ENNReal.ofReal
        (lemma77SignedTranslatedHorizontalKernel
          (300 * C32) c32 shift fpGap ((r : ℤ) + shift)) :=
      congrArg ENNReal.ofReal
        (lemma77HorizontalPointwiseKernel_sq_eq_signedTranslated
          (C := 300 * C32) (r := c32) hc32.le shift fpGap r)
    _ ≤ ENNReal.ofReal
        (2 * Real.exp (c32 ^ 2) *
          lemma77SignedTranslatedHorizontalKernel
            (300 * C32) (c32 / 2) shift fpGap center) :=
      ENNReal.ofReal_le_ofReal hkernel

/-- Uniform fixed-fresh horizontal mass bound with all three losses visible:
closed-window cardinality, radius comparison, and sparse-center averaging. -/
theorem
    lemma79CanonicalFirstPassageHorizontalPMF_nearSigmaEvent_outerMeasure_le_explicit :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (entry : TaoSection7RenewalPoint) (fpGap p R : ℕ)
        (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
        (sMin K B : ℝ) (fresh : List TaoSection7RenewalPoint),
        TaoSection7TriangleFamilyPairwiseDisjoint family →
        TaoSection7Triangle.lemma710GapAbsorbs K B sMin →
        (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) →
        1 ≤ sigmaSeparationScale sMin →
        (sigmaSeparationScale sMin) ^ 2 ≤ 1 + (fpGap : ℝ) →
        (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
            (lemma79EndpointFreshNearSigmaHorizontalEvent
              entry family old sMin K B p R fresh) ≤
          ((2 * R + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal
              (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_pointwiseKernel with
    ⟨C32, c32, hC32, hc32, hcanonical⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro entry fpGap p R family old sMin K B fresh
    hpair habsorb hRwidth hscale hsepwidth
  let shift := lemma79EndpointFreshHorizontalShift entry p fresh
  let amplitude : ℝ := 2 * Real.exp (c32 ^ 2)
  let kernel : ℤ → ℝ := fun z =>
    lemma77SignedTranslatedHorizontalKernel
      (300 * C32) (c32 / 2) shift fpGap z
  let centerBound : ℤ → ENNReal := fun z =>
    ENNReal.ofReal (amplitude * kernel z)
  let sparseBound : ℝ :=
    (2 * Real.exp ((c32 / 2) ^ 2) /
        (Nat.floor (sigmaSeparationScale sMin) : ℝ)) *
      ((300 * C32) *
        (lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) +
          lemma77HorizontalLinearCountConstant (c32 / 4)))
  have hC300 : 0 ≤ 300 * C32 :=
    mul_nonneg (by norm_num) hC32
  have hAmplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    positivity
  have hkernel0 (z : ℤ) : 0 ≤ kernel z := by
    exact lemma77SignedTranslatedHorizontalKernel_nonneg
      hC300 shift fpGap z
  have hkernelSummable :
      Summable fun c : sigmaHorizontalCenters family old sMin K B =>
        kernel c.1 := by
    simpa only [kernel, Function.comp_apply] using
      (lemma77SignedTranslatedHorizontalKernel_summable
        (C := 300 * C32) (r := c32 / 2)
        (half_pos hc32) shift fpGap).comp_injective
          Subtype.val_injective
  have hcenterSummable :
      Summable fun c : sigmaHorizontalCenters family old sMin K B =>
        amplitude * kernel c.1 :=
    hkernelSummable.mul_left amplitude
  have hcenter0 :
      ∀ c : sigmaHorizontalCenters family old sMin K B,
        0 ≤ amplitude * kernel c.1 :=
    fun c => mul_nonneg hAmplitude (hkernel0 c.1)
  have hcenterReal :
      (∑' c : sigmaHorizontalCenters family old sMin K B,
        kernel c.1) ≤ sparseBound := by
    have hsparse :=
      lemma77SignedTranslatedHorizontalKernel_tsum_sigma_le
        (old := old) hpair habsorb hC300 hc32 shift fpGap hscale hsepwidth
    rw [tsum_sigma_eq_tsum_horizontalCenters] at hsparse
    simpa only [kernel, sparseBound] using hsparse
  have hcenterENNReal :
      (∑' c : sigmaHorizontalCenters family old sMin K B,
        centerBound c.1) ≤
          ENNReal.ofReal (amplitude * sparseBound) := by
    change
      (∑' c : sigmaHorizontalCenters family old sMin K B,
        ENNReal.ofReal (amplitude * kernel c.1)) ≤
          ENNReal.ofReal (amplitude * sparseBound)
    rw [← ENNReal.ofReal_tsum_of_nonneg hcenter0 hcenterSummable]
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hcenterReal hAmplitude
  have hwindow :=
    lemma79CanonicalFirstPassageHorizontalPMF_nearSigmaEvent_outerMeasure_le_windowBounds
      entry fpGap p R family old sMin K B fresh centerBound
      (by
        intro center r hr
        exact
          lemma79CanonicalFirstPassageHorizontalPMF_windowAtom_le_signedCenter
            hC32 hc32 hcanonical entry fpGap R shift center.1 r
              hRwidth (by simpa [shift] using hr))
  calc
    (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) ≤
      ((2 * R + 1 : ℕ) : ENNReal) *
        ∑' c : sigmaHorizontalCenters family old sMin K B,
          centerBound c.1 := hwindow
    _ ≤ ((2 * R + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal (amplitude * sparseBound) :=
      by gcongr
    _ = ((2 * R + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal
          (lemma79NearSigmaHorizontalCenterMassBound C32 c32 sMin) := by
      simp only [lemma79NearSigmaHorizontalCenterMassBound,
        amplitude, sparseBound]

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
