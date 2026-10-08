/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageTerminal
import Erdos1135SecondScale.Tao.Renewal.Lemma77PascalGaussian
import Erdos1135SecondScale.Tao.Renewal.Lemma77TerminalHoldMoment

/-!
# Concrete Canonical First-Passage Endpoint Estimate

This module closes Tao's pointwise Lemma 7.7 estimate for the canonical
countable first-passage endpoint PMF.  It composes the native terminal reindex
with the checked height potential, vertical smoothing, horizontal convolution,
and terminal Hold tail at rate `log (21/20)`.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- Concrete pointwise endpoint kernel bound for the canonical first-passage
law, with no finite source carrier or local-limit input. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_pointwiseKernel_log_21_div_20 :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ),
        (s : ℤ) < ell →
          lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) ≤
            ENNReal.ofReal
              (lemma77PointwiseEndpointKernel
                (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
                s r (relativeVerticalOvershoot s ell)) := by
  let alpha : ℝ := Real.log (21 / 20 : ℝ)
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  let hheight := lemma77HeightPotentialInput_oneHalf_one
  obtain ⟨C33, c33, h733⟩ :=
    lemma77VerticalSmoothing733Input_of_kernel_convolution
      hheight.constants.1 hheight.constants.2 halpha
  obtain ⟨C32, c32, h732⟩ :=
    lemma77HorizontalConvolution732Input_of_kernel_convolution
      halpha h733.constants.2.1 h733.constants.2.2
  have htail : Lemma77TerminalHoldPointTailInput (15 : ℝ) alpha := by
    simpa [alpha] using lemma77TerminalHoldPointTailInput_log_21_div_20
  have hcompat := lemma77TerminalExponentCompatible_of_gamma_eq_alpha
    (alpha := alpha) (beta := alpha) (gamma := alpha) rfl le_rfl
  have hcmp := lemma77ScaledEndpointAssemblyKernelComparisonInput_natural
    htail.constants.1 h732.constants.2.1 h732.constants.2.2
      htail.constants.2.le
  refine ⟨C32, c32, h732.constants.2.1, h732.constants.2.2, ?_⟩
  intro start s r ell hell
  let overshoot := relativeVerticalOvershoot s ell
  have hover : 0 ≤ overshoot :=
    (relativeVerticalOvershoot_pos_of_lt hell).le
  calc
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) ≤
        ENNReal.ofReal
          (lemma77EndpointTerminalSplitMass start r s overshoot) :=
      lemma77CanonicalFirstPassageEndpointPMF_apply_le_ofReal_terminalSplitMass
        start s r ell
    _ ≤ ENNReal.ofReal
        (lemma77PointwiseEndpointKernel
          (c32 ^ 2) c32 (15 * C32) alpha s r overshoot) :=
      ENNReal.ofReal_le_ofReal (by
        calc
          lemma77EndpointTerminalSplitMass start r s overshoot ≤
              15 * lemma77EndpointAssemblyMass alpha alpha alpha start
                (r : ℤ) s overshoot :=
            lemma77EndpointTerminalSplitMass_le_assembly_of_tail
              hheight h733 h732 htail hcompat start r s overshoot hover
          _ ≤ 15 * lemma77SignedPointwiseEndpointKernel C32 c32 alpha s
                (r : ℤ) overshoot := by
            exact mul_le_mul_of_nonneg_left
              (lemma77EndpointAssemblyMass_le_signedPointwiseKernel
                hheight h733 h732 start (r : ℤ) s overshoot)
              htail.constants.1
          _ ≤ lemma77PointwiseEndpointKernel
                (c32 ^ 2) c32 (15 * C32) alpha s r overshoot :=
            hcmp.scaled_signed_kernel_le_pointwise s r overshoot hover)

/-- Safe real projection of the native canonical pointwise endpoint theorem. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_pointwiseKernel_log_21_div_20_toReal :
    ∃ C32 c32 : ℝ, 0 ≤ C32 ∧ 0 < c32 ∧
      ∀ (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ),
        (s : ℤ) < ell →
          (lemma77CanonicalFirstPassageEndpointPMF start s (r, ell)).toReal ≤
            lemma77PointwiseEndpointKernel
              (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
              s r (relativeVerticalOvershoot s ell) := by
  rcases lemma77CanonicalFirstPassageEndpointPMF_pointwiseKernel_log_21_div_20
      with ⟨C32, c32, hC32, hc32, hpoint⟩
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro start s r ell hell
  have hnative := hpoint start s r ell hell
  have hkernel_nonneg :
      0 ≤ lemma77PointwiseEndpointKernel
        (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
        s r (relativeVerticalOvershoot s ell) := by
    unfold lemma77PointwiseEndpointKernel
    positivity
  calc
    (lemma77CanonicalFirstPassageEndpointPMF start s (r, ell)).toReal ≤
        (ENNReal.ofReal
          (lemma77PointwiseEndpointKernel
            (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
            s r (relativeVerticalOvershoot s ell))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hnative
    _ = lemma77PointwiseEndpointKernel
        (c32 ^ 2) c32 (15 * C32) (Real.log (21 / 20 : ℝ))
        s r (relativeVerticalOvershoot s ell) :=
      ENNReal.toReal_ofReal hkernel_nonneg

/-- Weaken the four-parameter endpoint kernel to one common horizontal and
vertical decay rate. -/
theorem lemma77PointwiseEndpointKernel_le_commonRate
    {Cpt cstrong cweak lambda C : ℝ}
    (hCpt : 0 ≤ Cpt) (hcstrong : 0 < cstrong)
    (hcweak : 0 < cweak) (hweakStrong : cweak ≤ cstrong)
    (hweakVertical : cweak ≤ lambda) (hconst : Cpt ≤ C)
    (s r : ℕ) (overshoot : ℤ) (hover : 0 ≤ overshoot) :
    lemma77PointwiseEndpointKernel
        (cstrong ^ 2) cstrong Cpt lambda s r overshoot ≤
      C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
        taoLemma22GaussianWeight (1 + s)
          (cweak * ((r : ℝ) - (s : ℝ) / 4)) *
        Real.exp (-cweak * (overshoot : ℝ)) := by
  have hC_nonneg : 0 ≤ C := hCpt.trans hconst
  have hheight := lemma77HeightPotentialKernel_le_of_const_rate
    hCpt hconst hcweak hweakStrong (r : ℤ) s
  have hvertical :
      Real.exp (-lambda * (overshoot : ℝ)) ≤
        Real.exp (-cweak * (overshoot : ℝ)) := by
    rw [Real.exp_le_exp]
    have hoverReal : (0 : ℝ) ≤ (overshoot : ℝ) := by exact_mod_cast hover
    nlinarith [mul_le_mul_of_nonneg_right hweakVertical hoverReal]
  have hmul := mul_le_mul hheight hvertical
    (le_of_lt (Real.exp_pos _))
    (lemma77HeightPotentialKernel_nonneg hC_nonneg (r : ℤ) s)
  unfold lemma77PointwiseEndpointKernel
  unfold lemma77HeightPotentialKernel at hmul
  simp [taoLemma22GaussianWeight] at hmul ⊢
  convert hmul using 1
  all_goals
    simp [lemma77CenteredHorizontalDisplacement, abs_of_pos hcstrong,
      pow_two]
    ring_nf
    simp

/-- Tao's source-literal Lemma 7.7 form with one common absolute decay rate. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_commonRate :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (start : TaoSection7RenewalPoint) (s r ell : ℕ),
        s < ell →
          (lemma77CanonicalFirstPassageEndpointPMF start s (r, (ell : ℤ))).toReal ≤
            C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
              taoLemma22GaussianWeight (1 + s)
                (c * ((r : ℝ) - (s : ℝ) / 4)) *
              Real.exp (-c * ((ell - s : ℕ) : ℝ)) := by
  rcases
      lemma77CanonicalFirstPassageEndpointPMF_pointwiseKernel_log_21_div_20_toReal
      with ⟨C32, c32, hC32, hc32, hpoint⟩
  let lambda : ℝ := Real.log (21 / 20 : ℝ)
  let c : ℝ := min c32 lambda
  let C : ℝ := 1 + 15 * C32
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc32 hlambda
  have hc_le_c32 : c ≤ c32 := by
    dsimp [c]
    exact min_le_left _ _
  have hc_le_lambda : c ≤ lambda := by
    dsimp [c]
    exact min_le_right _ _
  have hC : 0 < C := by
    dsimp [C]
    nlinarith
  have hCpt_le : 15 * C32 ≤ C := by
    dsimp [C]
    linarith
  refine ⟨C, c, hC, hc, ?_⟩
  intro start s r ell hell
  have hellInt : (s : ℤ) < (ell : ℤ) := by exact_mod_cast hell
  have hpointwise := hpoint start s r (ell : ℤ) hellInt
  let overshoot := relativeVerticalOvershoot s (ell : ℤ)
  have hover : 0 ≤ overshoot :=
    (relativeVerticalOvershoot_pos_of_lt hellInt).le
  have hweaken := lemma77PointwiseEndpointKernel_le_commonRate
    (hCpt := mul_nonneg (by norm_num) hC32) hc32 hc hc_le_c32
    hc_le_lambda hCpt_le s r overshoot hover
  have hover_eq : overshoot = ((ell - s : ℕ) : ℤ) := by
    dsimp [overshoot, relativeVerticalOvershoot]
    omega
  calc
    (lemma77CanonicalFirstPassageEndpointPMF start s (r, (ell : ℤ))).toReal ≤
        lemma77PointwiseEndpointKernel
          (c32 ^ 2) c32 (15 * C32) lambda s r overshoot := by
      simpa [lambda, overshoot] using hpointwise
    _ ≤ C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
          taoLemma22GaussianWeight (1 + s)
            (c * ((r : ℝ) - (s : ℝ) / 4)) *
          Real.exp (-c * (overshoot : ℝ)) := hweaken
    _ = C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
          taoLemma22GaussianWeight (1 + s)
            (c * ((r : ℝ) - (s : ℝ) / 4)) *
          Real.exp (-c * ((ell - s : ℕ) : ℝ)) := by
      rw [hover_eq]
      norm_cast

end TaoSection7Lemma77

end

end Tao
end Erdos1135SecondScale
