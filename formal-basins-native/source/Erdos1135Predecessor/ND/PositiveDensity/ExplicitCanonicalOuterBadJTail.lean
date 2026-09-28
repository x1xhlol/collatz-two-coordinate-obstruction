/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOuterBadJ

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

theorem explicitRenewal_preHorizontalMargin :
    (1 / 320 : ℝ) ≤ (4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : (9 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 51 := by norm_num
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_pow] at hl
  have hr : Real.log 9 / Real.log 2 ≤ (51 / 16 : ℝ) := by
    apply (div_le_iff₀ hlog2).mpr
    norm_num at hl
    linarith
  linarith

theorem explicitRenewal_preHorizontalTail (J : ℕ)
    (entry : TaoSection7RenewalPoint) (gap m : ℕ) (hm : 1 ≤ m)
    (hgap : (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
      {atom | 4 * m ≤ 5 * atom.1.1} ≤
        ENNReal.ofReal ((2 : ℝ) ^ 55 * Real.exp (-(1 / 2 ^ 36 : ℝ) * m)) := by
  let eta : ℝ := 4 / 5 - (Real.log 9 / Real.log 2) / 4
  have he : (1 / 320 : ℝ) ≤ eta := explicitRenewal_preHorizontalMargin
  have he0 : 0 ≤ eta := le_trans (by norm_num) he
  have heSq : (1 / 320 : ℝ) ^ 2 ≤ eta ^ 2 := pow_le_pow_left₀ (by norm_num) he 2
  have hquad := lemma79CanonicalPreHorizontalQuadraticRate_le hm hgap
  change (5 / 21 : ℝ) * eta ^ 2 * m ≤ (eta * m) ^ 2 / (1 + (gap : ℝ)) at hquad
  have hcg : (1 / 2 ^ 36 : ℝ) ≤ (1 / 32768 : ℝ) * (5 / 21 : ℝ) * eta ^ 2 := by
    norm_num at heSq ⊢
    nlinarith
  have hcl : (1 / 2 ^ 36 : ℝ) ≤ (1 / 256 : ℝ) * eta := by
    norm_num at he ⊢
    linarith
  have hgArg : (1 / 2 ^ 36 : ℝ) * m ≤
      (1 / 32768 : ℝ) * ((eta * m) ^ 2 / (1 + (gap : ℝ))) := by
    have h := mul_le_mul_of_nonneg_right hcg (Nat.cast_nonneg m)
    have hq := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 1 / 32768)
    nlinarith
  have hlArg : (1 / 2 ^ 36 : ℝ) * m ≤ (1 / 256 : ℝ) * (eta * m) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcl (Nat.cast_nonneg m)
  have hg := Real.exp_le_exp.mpr (neg_le_neg hgArg)
  have hl := Real.exp_le_exp.mpr (neg_le_neg hlArg)
  have hbound : (2 : ℝ) ^ 54 *
      (Real.exp (-(1 / 32768 : ℝ) * ((eta * m) ^ 2 / (1 + (gap : ℝ)))) +
       Real.exp (-(1 / 256 : ℝ) * (eta * m))) ≤
      (2 : ℝ) ^ 55 * Real.exp (-(1 / 2 ^ 36 : ℝ) * m) := by
    simp only [neg_mul] at hg hl ⊢
    norm_num only at hg hl ⊢
    nlinarith
  let project : ((ℕ × ℤ) × List TaoSection7RenewalPoint) → ℕ := fun atom => atom.1.1
  have hsubset : {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint |
      4 * m ≤ 5 * atom.1.1} ⊆
      project ⁻¹' lemma77CanonicalHorizontalDeviationEvent gap (eta * m) := by
    intro atom ha
    exact lemma79CanonicalPreHorizontalEvent_subset_deviation hgap ha
  calc
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom | 4 * m ≤ 5 * atom.1.1} ≤
      (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        (project ⁻¹' lemma77CanonicalHorizontalDeviationEvent gap (eta * m)) :=
      (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure.mono hsubset
    _ = (lemma77CanonicalFirstPassageHorizontalPMF entry gap).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent gap (eta * m)) := by
      rw [← PMF.toOuterMeasure_map_apply]
      rw [show (lemma79CanonicalEndpointFreshPMF J entry gap).map project =
          lemma77CanonicalFirstPassageHorizontalPMF entry gap from
        lemma79CanonicalEndpointFreshPMF_map_horizontal_eq J entry gap]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 54 *
        (Real.exp (-(1 / 32768 : ℝ) * ((eta * m) ^ 2 / (1 + (gap : ℝ)))) +
         Real.exp (-(1 / 256 : ℝ) * (eta * m)))) :=
      explicitRenewal_horizontalTail entry gap (mul_nonneg he0 (Nat.cast_nonneg m))
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

theorem explicitRenewal_outerBadJ_tail {P J : ℕ} (hPJ : P ≤ J)
    (entry : TaoSection7RenewalPoint) (gap m : ℕ) (hm : 1 ≤ m)
    (hgap : (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
      {atom | 9 * m ≤ 10 * (atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
      ((2 : ℝ) ^ 55 + Real.exp ((P : ℝ) / 2)) *
        Real.exp (-(1 / 2 ^ 36 : ℝ) * m) := by
  let μ := lemma79CanonicalEndpointFreshPMF J entry gap
  let BadPre : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
    {atom | 4 * m ≤ 5 * atom.1.1}
  let BadSuf : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
    {atom | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2}
  have hsubset : {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint |
      9 * m ≤ 10 * (atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2)} ⊆
      BadPre ∪ BadSuf := by
    intro atom ha
    by_cases hp : 4 * m ≤ 5 * atom.1.1
    · exact Or.inl hp
    · right
      dsimp [BadSuf]
      simp only [Set.mem_setOf_eq] at ha
      omega
  have hraw : μ.toOuterMeasure
      {atom | 9 * m ≤ 10 * (atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2)} ≤
      μ.toOuterMeasure BadPre + μ.toOuterMeasure BadSuf := by
    calc
      _ ≤ μ.toOuterMeasure (BadPre ∪ BadSuf) := μ.toOuterMeasure.mono hsubset
      _ ≤ _ := MeasureTheory.measure_union_le BadPre BadSuf
  have hpre := explicitRenewal_preHorizontalTail J entry gap m hm hgap
  have hsuf := lemma79CanonicalEndpointFreshPMF_suffixHorizontalTail_outerMeasure_le hPJ entry gap m
  have hreal := ENNReal.toReal_mono (by
      simp only [ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, or_self, not_false_eq_true] : ENNReal.ofReal
      ((2 : ℝ) ^ 55 * Real.exp (-(1 / 2 ^ 36 : ℝ) * m)) +
      ENNReal.ofReal (Real.exp ((P : ℝ) / 2 - (m : ℝ) / 160)) ≠ ⊤)
    (hraw.trans (add_le_add hpre hsuf))
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hreal
  have hExp : Real.exp ((P : ℝ) / 2 - (m : ℝ) / 160) ≤
      Real.exp ((P : ℝ) / 2) * Real.exp (-(1 / 2 ^ 36 : ℝ) * m) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hm0 := Nat.cast_nonneg (α := ℝ) m
    norm_num
    linarith
  change _ ≤ _ at hreal
  calc
    _ ≤ (2 : ℝ) ^ 55 * Real.exp (-(1 / 2 ^ 36 : ℝ) * m) +
        Real.exp ((P : ℝ) / 2 - (m : ℝ) / 160) := hreal
    _ ≤ (2 : ℝ) ^ 55 * Real.exp (-(1 / 2 ^ 36 : ℝ) * m) +
        Real.exp ((P : ℝ) / 2) * Real.exp (-(1 / 2 ^ 36 : ℝ) * m) := add_le_add le_rfl hExp
    _ = _ := by ring

end

end Erdos1135Predecessor.ND.PositiveDensity
