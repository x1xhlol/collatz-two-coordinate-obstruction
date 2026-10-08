/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalFirstPassagePointwise
import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageLocalizedMass

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open scoped BigOperators

noncomputable section

theorem explicitRenewal_horizontalPMF_le
    (start : TaoSection7RenewalPoint) (s r : ℕ) :
    lemma77CanonicalFirstPassageHorizontalPMF start s r ≤
      ENNReal.ofReal (lemma77HorizontalPointwiseKernel
        ((1 / 128 : ℝ) ^ 2) (1 / 128) (300 * 2 ^ 21) s r) := by
  rw [lemma77CanonicalFirstPassageHorizontalPMF_apply_eq_tsum_overshoot]
  calc
    _ ≤ ∑' u : ℕ, ENNReal.ofReal (lemma77PointwiseEndpointKernel
        ((1 / 128 : ℝ) ^ 2) (1 / 128) (15 * 2 ^ 21) (Real.log (21 / 20 : ℝ))
        s r ((u + 1 : ℕ) : ℤ)) := by
      apply ENNReal.tsum_le_tsum
      intro u
      have hover : relativeVerticalOvershoot s ((s : ℤ) + 1 + (u : ℤ)) =
          ((u + 1 : ℕ) : ℤ) := by unfold relativeVerticalOvershoot; omega
      simpa only [hover] using explicitRenewal_endpointPMF_le start s r
        ((s : ℤ) + 1 + (u : ℤ)) (by omega)
    _ = ENNReal.ofReal (∑' u : ℕ, lemma77PointwiseEndpointKernel
        ((1 / 128 : ℝ) ^ 2) (1 / 128) (15 * 2 ^ 21) (Real.log (21 / 20 : ℝ))
        s r ((u + 1 : ℕ) : ℤ)) := by
      symm
      apply ENNReal.ofReal_tsum_of_nonneg
      · intro u
        unfold lemma77PointwiseEndpointKernel
        positivity
      · unfold lemma77PointwiseEndpointKernel
        simp only [Int.cast_natCast]
        exact lemma77_summable_exp_neg_log_21_div_20_positiveOvershoot.mul_left _
    _ = _ := by rw [lemma77_tsum_pointwiseEndpointKernel_positiveOvershoot]

theorem explicitRenewal_horizontalTail_envelope
    (start : TaoSection7RenewalPoint) (s : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
      (lemma77CanonicalHorizontalDeviationEvent s t) ≤
        ENNReal.ofReal (lemma77HorizontalDeviationTailEnvelope
          ((1 / 128 : ℝ) ^ 2) (1 / 128) (300 * 2 ^ 21) s t) := by
  let f : ℕ → ℝ := lemma77HorizontalPointwiseKernel
    ((1 / 128 : ℝ) ^ 2) (1 / 128) (300 * 2 ^ 21) s
  have hf0 (r : ℕ) : 0 ≤ f r := by dsimp [f, lemma77HorizontalPointwiseKernel]; positivity
  have hf : Summable f := lemma77HorizontalPointwiseKernel_summable
    (by norm_num) (by norm_num) s
  apply le_trans (pmf_toOuterMeasure_le_of_apply_le_ofReal
    (lemma77CanonicalFirstPassageHorizontalPMF start s)
    (lemma77CanonicalHorizontalDeviationEvent s t) f hf0 (hf.indicator _)
    (fun r _ => explicitRenewal_horizontalPMF_le start s r))
  apply ENNReal.ofReal_le_ofReal
  exact lemma77HorizontalPointwiseKernel_deviation_tsum_le
    (by norm_num) (by norm_num) (by positivity) ht s

theorem explicitRenewal_verticalTail_envelope
    (start : TaoSection7RenewalPoint) (s T : ℕ) (hT : 1 ≤ T) :
    (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
      (lemma77CanonicalVerticalOvershootTailEvent s T) ≤
        ENNReal.ofReal (lemma77VerticalOvershootTailEnvelope
          ((1 / 128 : ℝ) ^ 2) (1 / 128) (15 * 2 ^ 21) T) := by
  let f : ℕ × ℤ → ℝ := fun x => lemma77PointwiseEndpointKernel
    ((1 / 128 : ℝ) ^ 2) (1 / 128) (15 * 2 ^ 21) (Real.log (21 / 20 : ℝ))
    s x.1 (relativeVerticalOvershoot s x.2)
  have hf0 (x : ℕ × ℤ) : 0 ≤ f x := by dsimp [f, lemma77PointwiseEndpointKernel]; positivity
  have hf : Summable ((lemma77CanonicalVerticalOvershootTailEvent s T).indicator f) :=
    lemma77PointwiseEndpointKernel_verticalTail_summable
      (by norm_num) (by norm_num) (by positivity)
      (by linarith [explicitRenewal_log_bounds.1]) s T
  apply le_trans (pmf_toOuterMeasure_le_of_apply_le_ofReal
    (lemma77CanonicalFirstPassageEndpointPMF start s)
    (lemma77CanonicalVerticalOvershootTailEvent s T) f hf0 hf (fun x hx => ?_))
  · exact ENNReal.ofReal_le_ofReal (lemma77PointwiseEndpointKernel_verticalTail_tsum_le
      (by norm_num) (by norm_num) (by positivity) s T)
  · have hx' : (s : ℤ) + (T : ℤ) ≤ x.2 := hx
    exact explicitRenewal_endpointPMF_le start s x.1 x.2 (by omega)

theorem explicitRenewal_gaussianCount_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    lemma77HorizontalGaussianCountConstant a ≤ 64 / a := by
  have he : Real.exp (5 * a / 64) ≤ 2 := by
    apply le_trans (Real.exp_bound_div_one_sub_of_interval
      (by positivity : 0 ≤ 5 * a / 64) (by linarith : 5 * a / 64 < 1))
    apply (div_le_iff₀ (by linarith : 0 < 1 - 5 * a / 64)).mpr
    linarith
  unfold lemma77HorizontalGaussianCountConstant
  calc
    _ = 32 * (Real.exp ((a / 16) / 4) * Real.exp (a / 16)) / a := by ring
    _ = 32 * Real.exp (5 * a / 64) / a := by
      rw [← Real.exp_add]
      rw [show (a / 16) / 4 + a / 16 = 5 * a / 64 by ring]
    _ ≤ 64 / a := div_le_div_of_nonneg_right (by linarith) ha.le

theorem explicitRenewal_linearCount_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    lemma77HorizontalLinearCountConstant b ≤ 16 / b := by
  have he : Real.exp (-(b / 4)) ≤ 1 / (1 + b / 4) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith [Real.add_one_le_exp (b / 4)]
  have he' : Real.exp (-(b / 4)) ≤ 1 - b / 8 := by
    apply he.trans
    apply (div_le_iff₀ (by positivity : 0 < 1 + b / 4)).mpr
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb1)]
  have hgap : b / 8 ≤ 1 - Real.exp (-(b / 4)) := by linarith
  unfold lemma77HorizontalLinearCountConstant
  rw [← div_eq_mul_inv]
  calc
    _ ≤ 2 / (b / 8) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hgap
    _ = 16 / b := by ring

theorem explicitRenewal_horizontalTail
    (start : TaoSection7RenewalPoint) (s : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
      (lemma77CanonicalHorizontalDeviationEvent s t) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 54 *
          (Real.exp (-(1 / 32768 : ℝ) * (t ^ 2 / (1 + (s : ℝ)))) +
            Real.exp (-(1 / 256 : ℝ) * t))) := by
  have hG : lemma77HorizontalGaussianCountConstant (((1 / 128 : ℝ) ^ 2) / 2) ≤ 2 ^ 21 := by
    have h := explicitRenewal_gaussianCount_le
      (by norm_num : (0 : ℝ) < ((1 / 128 : ℝ) ^ 2) / 2) (by norm_num)
    norm_num at h ⊢
    exact h
  have hL : lemma77HorizontalLinearCountConstant ((1 / 128 : ℝ) / 2) ≤ 2 ^ 12 := by
    have h := explicitRenewal_linearCount_le
      (by norm_num : (0 : ℝ) < (1 / 128 : ℝ) / 2) (by norm_num)
    norm_num at h ⊢
    exact h
  have hCG : (300 * 2 ^ 21 : ℝ) *
      lemma77HorizontalGaussianCountConstant (((1 / 128 : ℝ) ^ 2) / 2) ≤ 2 ^ 54 := by
    norm_num at hG ⊢
    linarith
  have hCL : (300 * 2 ^ 21 : ℝ) *
      lemma77HorizontalLinearCountConstant ((1 / 128 : ℝ) / 2) ≤ 2 ^ 54 := by
    norm_num at hL ⊢
    linarith
  apply (explicitRenewal_horizontalTail_envelope start s ht).trans
  apply ENNReal.ofReal_le_ofReal
  unfold lemma77HorizontalDeviationTailEnvelope
  have h1 := mul_le_mul_of_nonneg_right hCG
    (Real.exp_pos (-(((1 / 128 : ℝ) ^ 2) / 2) * (t ^ 2 / (1 + (s : ℝ))))).le
  have h2 := mul_le_mul_of_nonneg_right hCL
    (Real.exp_pos (-((1 / 128 : ℝ) / 2) * t)).le
  norm_num at h1 h2 ⊢
  nlinarith

theorem explicitRenewal_verticalTail
    (start : TaoSection7RenewalPoint) (s T : ℕ) (hT : 1 ≤ T) :
    (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
      (lemma77CanonicalVerticalOvershootTailEvent s T) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 54 * Real.exp (-(1 / 32 : ℝ) * (T : ℝ))) := by
  have hG : lemma77HorizontalGaussianCountConstant ((1 / 128 : ℝ) ^ 2) ≤ 2 ^ 20 := by
    have h := explicitRenewal_gaussianCount_le
      (by norm_num : (0 : ℝ) < (1 / 128 : ℝ) ^ 2) (by norm_num)
    norm_num at h ⊢
    exact h
  have hL : lemma77HorizontalLinearCountConstant (1 / 128 : ℝ) ≤ 2 ^ 11 := by
    have h := explicitRenewal_linearCount_le (by norm_num : (0 : ℝ) < 1 / 128) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcoeff : (21 * (15 * 2 ^ 21) : ℝ) *
      (lemma77HorizontalGaussianCountConstant ((1 / 128 : ℝ) ^ 2) +
        lemma77HorizontalLinearCountConstant (1 / 128 : ℝ)) ≤ 2 ^ 54 := by
    norm_num at hG hL ⊢
    linarith
  have hexp : Real.exp (-(Real.log (21 / 20 : ℝ) * (T : ℝ))) ≤
      Real.exp (-(1 / 32 : ℝ) * (T : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right explicitRenewal_log_bounds.1 (Nat.cast_nonneg T)
    nlinarith
  apply (explicitRenewal_verticalTail_envelope start s T hT).trans
  apply ENNReal.ofReal_le_ofReal
  unfold lemma77VerticalOvershootTailEnvelope
  exact mul_le_mul hcoeff hexp (Real.exp_pos _).le (by positivity)

theorem explicitRenewal_threeFifthsTail
    (start : TaoSection7RenewalPoint) (s : ℕ) (hs : 1 ≤ s) :
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
      (lemma77CanonicalHorizontalDeviationEvent s ((s : ℝ) ^ (3 / 5 : ℝ))) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 55 *
          Real.exp (-(1 / 65536 : ℝ) * ((s : ℝ) ^ (1 / 5 : ℝ)))) := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hp := lemma77_threeFifths_sq_div_one_add_ge_half_oneFifth hs'
  have hl : (s : ℝ) ^ (1 / 5 : ℝ) ≤ (s : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs' (by norm_num)
  have hy : 0 ≤ (s : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg s) _
  have hEg : Real.exp (-(1 / 32768 : ℝ) *
      (((s : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (1 + (s : ℝ)))) ≤
      Real.exp (-(1 / 65536 : ℝ) * ((s : ℝ) ^ (1 / 5 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hEl : Real.exp (-(1 / 256 : ℝ) * ((s : ℝ) ^ (3 / 5 : ℝ))) ≤
      Real.exp (-(1 / 65536 : ℝ) * ((s : ℝ) ^ (1 / 5 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  apply (explicitRenewal_horizontalTail start s (Real.rpow_nonneg (Nat.cast_nonneg s) _)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2 : ℝ) ^ 54 *
        (Real.exp (-(1 / 65536 : ℝ) * ((s : ℝ) ^ (1 / 5 : ℝ))) +
          Real.exp (-(1 / 65536 : ℝ) * ((s : ℝ) ^ (1 / 5 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (add_le_add hEg hEl) (by positivity)
    _ = _ := by ring

private theorem exp_quarter_budget (K x : ℝ) (hbudget : 4 * K ≤ 1 + x) :
    K * Real.exp (-x) ≤ 1 / 4 := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos x)).mpr
  linarith [Real.add_one_le_exp x]

theorem explicitRenewal_quarterTailRadius {B : ℕ} (hB : 2 ^ 80 ≤ B)
    (start : TaoSection7RenewalPoint) (s : ℕ) :
    (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
      (lemma77CanonicalHorizontalDeviationEvent s
        ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))) ≤ ENNReal.ofReal (1 / 4 : ℝ) ∧
    (lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
      (lemma77CanonicalVerticalOvershootTailEvent s B) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have hB' : (2 : ℝ) ^ 80 ≤ B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by norm_num only at hB'; linarith
  have hBN : 1 ≤ B := by exact_mod_cast hB1
  let S : ℝ := 1 + (s : ℝ)
  let t : ℝ := (B : ℝ) * Real.sqrt S
  have hS : 0 < S := by dsimp [S]; positivity
  have hroot : 1 ≤ Real.sqrt S := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (Nat.cast_nonneg s))
  have ht : (B : ℝ) ≤ t := by dsimp [t]; nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hquad : t ^ 2 / S = (B : ℝ) ^ 2 := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt hS.le]
    field_simp
  have hEg : Real.exp (-(1 / 32768 : ℝ) * (t ^ 2 / S)) ≤
      Real.exp (-(1 / 32768 : ℝ) * (B : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [hquad]
    nlinarith
  have hEl : Real.exp (-(1 / 256 : ℝ) * t) ≤
      Real.exp (-(1 / 32768 : ℝ) * (B : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hHB : (2 : ℝ) ^ 55 * Real.exp (-((B : ℝ) / 32768)) ≤ 1 / 4 := by
    apply exp_quarter_budget
    norm_num only at hB' ⊢
    linarith
  have hVB : (2 : ℝ) ^ 54 * Real.exp (-((B : ℝ) / 32)) ≤ 1 / 4 := by
    apply exp_quarter_budget
    norm_num only at hB' ⊢
    linarith
  constructor
  · apply (explicitRenewal_horizontalTail start s ht0).trans
    apply ENNReal.ofReal_le_ofReal
    change (2 : ℝ) ^ 54 * (Real.exp (-(1 / 32768 : ℝ) * (t ^ 2 / S)) +
      Real.exp (-(1 / 256 : ℝ) * t)) ≤ 1 / 4
    have hEq : -((B : ℝ) / 32768) = -(1 / 32768 : ℝ) * (B : ℝ) := by ring
    rw [hEq] at hHB
    calc
      _ ≤ (2 : ℝ) ^ 54 * (Real.exp (-(1 / 32768 : ℝ) * (B : ℝ)) +
          Real.exp (-(1 / 32768 : ℝ) * (B : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hEg hEl) (by positivity)
      _ = (2 : ℝ) ^ 55 * Real.exp (-(1 / 32768 : ℝ) * (B : ℝ)) := by ring
      _ ≤ 1 / 4 := hHB
  · apply (explicitRenewal_verticalTail start s B hBN).trans
    apply ENNReal.ofReal_le_ofReal
    have hEq : -((B : ℝ) / 32) = -(1 / 32 : ℝ) * (B : ℝ) := by ring
    rw [hEq] at hVB
    exact hVB

theorem explicitRenewal_localized_mass {B : ℕ} (hB : 2 ^ 80 ≤ B)
    (start : TaoSection7RenewalPoint) (s : ℕ) :
    (1 / 2 : ℝ) ≤ ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
      (lemma77CanonicalLocalizedEndpointEvent s B)).toReal := by
  let p := lemma77CanonicalFirstPassageEndpointPMF start s
  let H : Set (ℕ × ℤ) := Prod.fst ⁻¹' lemma77CanonicalHorizontalDeviationEvent s
    ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))
  let V : Set (ℕ × ℤ) := lemma77CanonicalVerticalOvershootTailEvent s B
  have htail := explicitRenewal_quarterTailRadius hB start s
  have hHlift : p.toOuterMeasure H =
      (lemma77CanonicalFirstPassageHorizontalPMF start s).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent s ((B : ℝ) * Real.sqrt (1 + (s : ℝ)))) := by
    exact (PMF.toOuterMeasure_map_apply Prod.fst p
        (lemma77CanonicalHorizontalDeviationEvent s
          ((B : ℝ) * Real.sqrt (1 + (s : ℝ))))).symm
  have hH : (p.toOuterMeasure H).toReal ≤ 1 / 4 := by
    rw [hHlift]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htail.1).trans_eq
      (ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hV : (p.toOuterMeasure V).toReal ≤ 1 / 4 :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top htail.2).trans_eq
      (ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hgood := pmf_compl_union_toReal_ge_half p H V hH hV
  have hevent : lemma77CanonicalLocalizedEndpointEvent s B = (H ∪ V)ᶜ := by
    ext x
    simp [lemma77CanonicalLocalizedEndpointEvent, H, V,
      lemma77CanonicalHorizontalDeviationEvent, lemma77CanonicalVerticalOvershootTailEvent]
  rw [hevent]
  exact hgood

end

end Erdos1135Predecessor.ND.PositiveDensity
