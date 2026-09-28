/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitPolynomialGeometricTail
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTerminal
import Erdos1135Predecessor.Tao.Renewal.Lemma77PascalGaussian
import Erdos1135Predecessor.Tao.Renewal.Lemma77TerminalHoldMoment

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open scoped BigOperators

noncomputable section

theorem explicitRenewal_log_bounds :
    (1 / 21 : ℝ) ≤ Real.log (21 / 20 : ℝ) ∧
      Real.log (21 / 20 : ℝ) ≤ 1 / 20 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 21 / 20)
    norm_num at h ⊢
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 20)
    norm_num at h ⊢
    exact h

theorem explicitRenewal_exp_neg_le {delta : ℝ} (hdelta : 1 / 42 ≤ delta) :
    Real.exp (-delta) ≤ (42 / 43 : ℝ) := by
  rw [Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ (Real.exp_pos delta)).mpr
  have h := Real.add_one_le_exp delta
  nlinarith

theorem explicitRenewal_exp_neg_mul_le {delta : ℝ} (hdelta : 1 / 42 ≤ delta)
    (n : ℕ) : Real.exp (-(delta * (n : ℝ))) ≤ (42 / 43 : ℝ) ^ n := by
  rw [show -(delta * (n : ℝ)) = (n : ℝ) * (-delta) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (explicitRenewal_exp_neg_le hdelta) n

theorem explicitRenewal_shifted_exp_tsum_le {delta : ℝ}
    (hdelta : 1 / 42 ≤ delta) :
    (∑' q : ℕ, Real.exp (-(delta * ((q + 1 : ℕ) : ℝ)))) ≤ 43 := by
  have hd : 0 < delta := by linarith
  have hs : Summable (fun q : ℕ => Real.exp (-(delta * ((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable hd).comp_injective Nat.succ_injective
  obtain ⟨hg, hb⟩ := polynomialGeometric_moment_le 0
    (by norm_num : (0 : ℝ) ≤ 42 / 43) (by norm_num : (42 / 43 : ℝ) < 1)
  simp only [pow_zero, one_mul] at hg hb
  have hpoint (q : ℕ) : Real.exp (-(delta * ((q + 1 : ℕ) : ℝ))) ≤
      (42 / 43 : ℝ) ^ q := by
    apply le_trans (b := Real.exp (-(delta * (q : ℝ)))) _
      (explicitRenewal_exp_neg_mul_le hdelta q)
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  exact (hs.tsum_le_tsum hpoint hg).trans (by norm_num at hb ⊢; exact hb)

theorem explicitRenewal_heightScaleConvolution_le {delta : ℝ}
    (hdelta : 1 / 42 ≤ delta) (s : ℕ) :
    (∑ lp ∈ Finset.range (s + 1),
      Real.exp (-(delta * (lp : ℝ))) *
        ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))) ≤
      (43 : ℝ) ^ 2 * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  have hH : 0 ≤ H := Real.rpow_nonneg (by positivity) _
  obtain ⟨hs, hb⟩ := polynomialGeometric_moment_le 1
    (by norm_num : (0 : ℝ) ≤ 42 / 43) (by norm_num : (42 / 43 : ℝ) < 1)
  simp only [pow_one] at hs hb
  have hsum : (∑ lp ∈ Finset.range (s + 1),
      ((lp + 1 : ℕ) : ℝ) * (42 / 43 : ℝ) ^ lp) ≤ (43 : ℝ) ^ 2 := by
    exact (hs.sum_le_tsum (Finset.range (s + 1)) (by intro i _; positivity)).trans
      (by norm_num at hb ⊢; exact hb)
  calc
    _ ≤ ∑ lp ∈ Finset.range (s + 1),
        (((lp + 1 : ℕ) : ℝ) * (42 / 43 : ℝ) ^ lp) * H := by
      apply Finset.sum_le_sum
      intro lp hlp
      have hscale := lemma77VerticalSmoothing733_heightScaleTerm_le s lp
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hlp))
      calc
        _ ≤ Real.exp (-(delta * (lp : ℝ))) * ((1 + (lp : ℝ)) * H) :=
          mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le
        _ ≤ (42 / 43 : ℝ) ^ lp * ((1 + (lp : ℝ)) * H) :=
          mul_le_mul_of_nonneg_right (explicitRenewal_exp_neg_mul_le hdelta lp)
            (mul_nonneg (by positivity) hH)
        _ = _ := by push_cast; ring
    _ = (∑ lp ∈ Finset.range (s + 1),
        ((lp + 1 : ℕ) : ℝ) * (42 / 43 : ℝ) ^ lp) * H := by rw [Finset.sum_mul]
    _ ≤ (43 : ℝ) ^ 2 * H := mul_le_mul_of_nonneg_right hsum hH

theorem explicitRenewal_verticalSmoothing :
    Lemma77VerticalSmoothing733Input (1 / 2) 1 (Real.log (21 / 20 : ℝ))
      (43 ^ 2) (Real.log (21 / 20 : ℝ)) := by
  let alpha : ℝ := Real.log (21 / 20 : ℝ)
  have hlo : (1 / 21 : ℝ) ≤ alpha := explicitRenewal_log_bounds.1
  have hhi : alpha ≤ (1 / 20 : ℝ) := explicitRenewal_log_bounds.2
  have ha : 0 < alpha := by linarith
  refine ⟨⟨ha, by positivity, ha⟩, ?_⟩
  intro j s
  have hh := lemma77VerticalSmoothing733KernelSum_le_heightKernel_of_heightScale
    (C := (1 / 2 : ℝ)) (c := 1) (beta := alpha) (K := (43 : ℝ) ^ 2)
    (c33 := alpha) (by norm_num) (by norm_num) (by positivity) ha
    (by linarith) (by linarith) (by nlinarith [sq_nonneg (alpha - 1 / 20)])
    (by nlinarith [sq_nonneg (alpha - 1 / 20)])
    (explicitRenewal_heightScaleConvolution_le (by linarith : 1 / 42 ≤ alpha / 2)) j s
  convert hh using 1
  norm_num [alpha]

theorem explicitRenewal_horizontalConvolution :
    Lemma77HorizontalConvolution732Input (Real.log (21 / 20 : ℝ))
      (43 ^ 2) (Real.log (21 / 20 : ℝ)) (2 ^ 21) (1 / 128) := by
  let alpha : ℝ := Real.log (21 / 20 : ℝ)
  have hlo : (1 / 21 : ℝ) ≤ alpha := explicitRenewal_log_bounds.1
  have ha : 0 < alpha := by linarith
  have h2 : 2 * (1 / 128 : ℝ) ≤ alpha := by linarith
  have h4 : 4 * (1 / 128 : ℝ) ≤ alpha := by linarith
  refine ⟨⟨ha, by positivity, by norm_num⟩, ?_, ?_⟩
  · intro j s
    simpa [neg_mul] using lemma77HorizontalConvolution732Kernel_summable
      (C := (43 : ℝ) ^ 2) (by positivity) ha ha (by norm_num : (0 : ℝ) < 1 / 128)
      h2 h4 j s
  · intro j s
    have hA := explicitRenewal_shifted_exp_tsum_le (by linarith : 1 / 42 ≤ alpha)
    have hB := explicitRenewal_shifted_exp_tsum_le (by linarith : 1 / 42 ≤ alpha / 2)
    apply le_trans (lemma77HorizontalConvolution732KernelTsum_le_heightKernel
      (C := (43 : ℝ) ^ 2) (by positivity) ha ha (by norm_num : (0 : ℝ) < 1 / 128)
      h2 h4 j s)
    apply lemma77HeightPotentialKernel_const_mono
    norm_num at hA hB ⊢
    nlinarith

theorem explicitRenewal_endpointPMF_le
    (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ) (hell : (s : ℤ) < ell) :
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) ≤
      ENNReal.ofReal (lemma77PointwiseEndpointKernel
        ((1 / 128 : ℝ) ^ 2) (1 / 128) (15 * 2 ^ 21) (Real.log (21 / 20 : ℝ))
        s r (relativeVerticalOvershoot s ell)) := by
  let alpha : ℝ := Real.log (21 / 20 : ℝ)
  let hheight := lemma77HeightPotentialInput_oneHalf_one
  have h733 := explicitRenewal_verticalSmoothing
  have h732 := explicitRenewal_horizontalConvolution
  have htail : Lemma77TerminalHoldPointTailInput (15 : ℝ) alpha :=
    lemma77TerminalHoldPointTailInput_log_21_div_20
  have hcompat := lemma77TerminalExponentCompatible_of_gamma_eq_alpha
    (alpha := alpha) (beta := alpha) (gamma := alpha) rfl le_rfl
  have hcmp := lemma77ScaledEndpointAssemblyKernelComparisonInput_natural
    htail.constants.1 h732.constants.2.1 h732.constants.2.2 htail.constants.2.le
  let overshoot := relativeVerticalOvershoot s ell
  have hover : 0 ≤ overshoot := (relativeVerticalOvershoot_pos_of_lt hell).le
  calc
    _ ≤ ENNReal.ofReal (lemma77EndpointTerminalSplitMass start r s overshoot) :=
      lemma77CanonicalFirstPassageEndpointPMF_apply_le_ofReal_terminalSplitMass start s r ell
    _ ≤ ENNReal.ofReal (lemma77PointwiseEndpointKernel
        ((1 / 128 : ℝ) ^ 2) (1 / 128) (15 * 2 ^ 21) alpha s r overshoot) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 15 * lemma77EndpointAssemblyMass alpha alpha alpha start (r : ℤ) s overshoot :=
          lemma77EndpointTerminalSplitMass_le_assembly_of_tail
            hheight h733 h732 htail hcompat start r s overshoot hover
        _ ≤ 15 * lemma77SignedPointwiseEndpointKernel (2 ^ 21) (1 / 128) alpha
            s (r : ℤ) overshoot :=
          mul_le_mul_of_nonneg_left
            (lemma77EndpointAssemblyMass_le_signedPointwiseKernel
              hheight h733 h732 start (r : ℤ) s overshoot) htail.constants.1
        _ ≤ _ := hcmp.scaled_signed_kernel_le_pointwise s r overshoot hover

end

end Erdos1135Predecessor.ND.PositiveDensity
