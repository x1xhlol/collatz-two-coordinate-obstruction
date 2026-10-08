/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageHorizontal
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageSignedSparse
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageSignedTotal
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeWindow

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open scoped BigOperators

open TaoSection7Lemma77

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79NearSigmaHorizontalCenterMassBound
    (C32 c32 sMin : ℝ) : ℝ :=
  (2 * Real.exp (c32 ^ 2)) *
    ((2 * Real.exp ((c32 / 2) ^ 2) /
        (Nat.floor (sigmaSeparationScale sMin) : ℝ)) *
      ((300 * C32) *
        (lemma77HorizontalGaussianCountConstant ((c32 / 4) ^ 2) +
          lemma77HorizontalLinearCountConstant (c32 / 4))))

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
