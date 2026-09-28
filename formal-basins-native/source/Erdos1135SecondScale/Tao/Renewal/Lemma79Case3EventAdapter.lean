/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79NativeMarkov

/-!
# Lemma 7.9 Canonical Case 3 Event Adapter

This proof leaf connects the canonical cutoff statistic to the existing Case 3
positive-white count.  It deliberately does not identify the zero-inclusive
canonical trace with the legacy positive-first-time stopping run.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The cutoff-gated white count is exactly the Case 3 positive-offset count
for the point-indexed source cutoff predicate. -/
theorem lemma79CutoffWhiteCount_eq_case3PositiveWhiteCount
    (pointAt : ℕ -> TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C t : ℕ) :
    lemma79CutoffWhiteCount pointAt n xi epsilon C t =
      taoSection7Case3PositiveWhiteCount
        (taoSection7Case3SourceCutoffPointW
          pointAt n xi epsilon C) t := by
  unfold lemma79CutoffWhiteCount taoSection7Case3PositiveWhiteCount
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply propext
  change
    (∃ hj : 0 < ((pointAt q).j : ℕ),
        ((pointAt q).j : ℕ) ≤ C ∧
          taoSection7SourceWhitePoint n xi epsilon
            ({j := ⟨(pointAt q).j, hj⟩, l := (pointAt q).l} :
              TaoSection7Point)) ↔
      ((pointAt q).j : ℕ) ≤ C ∧
        taoSection7SourceWhitePoint n xi epsilon (pointAt q)
  constructor
  · rintro ⟨hj, hjC, hwhite⟩
    refine ⟨hjC, ?_⟩
    have hpoint :
        ({j := ⟨(pointAt q).j, hj⟩, l := (pointAt q).l} :
            TaoSection7Point) = pointAt q := by
      have hjEq :
          (⟨(pointAt q).j, hj⟩ : ℕ+) = (pointAt q).j := by
        apply Subtype.ext
        rfl
      exact congrArg₂ TaoSection7Point.mk hjEq rfl
    simpa [hpoint] using hwhite
  · rintro ⟨hjC, hwhite⟩
    exact ⟨(pointAt q).j.property, hjC, hwhite⟩

/-- At every present canonical endpoint, the repaired tail moment is the
exponential of the existing Case 3 positive-white count. -/
theorem lemma79CutoffTailMoment_eq_case3PositiveWhiteCount_of_tR?
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C R t : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (ht : tR? (lemma79CutoffTrace pointAt family C) R = some t) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R =
      Real.exp
        (-(taoSection7Case3PositiveWhiteCount
              (taoSection7Case3SourceCutoffPointW
                pointAt n xi epsilon C) t : ℝ) +
          epsilon * (R : ℝ)) := by
  rw [lemma79CutoffTailMoment_eq_exp_of_tR? ht]
  rw [lemma79CutoffWhiteCount_eq_case3PositiveWhiteCount]

/-- The canonical real-valued shifted slack event on one iid Hold sample. -/
noncomputable def lemma79CanonicalFSlackEvent
    (origin : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C R Amarkov : ℕ) : Set (List TaoSection7RenewalPoint) :=
  {full |
    (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon <
      lemma79CutoffTailMoment
        (lemma79HoldPathPointAt origin full)
        family n xi epsilon C R}

/-- The real canonical slack event is exactly the strict native event used by
the countable Markov theorem. -/
theorem lemma79CanonicalFSlackEvent_eq_native
    (origin : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C R Amarkov : ℕ) :
    lemma79CanonicalFSlackEvent
        origin family n xi epsilon C R Amarkov =
      {full |
        (10 : ENNReal) ^ (Amarkov + 2) *
            ENNReal.ofReal (Real.exp epsilon) <
          lemma79HoldPathCutoffTailMomentENN
            origin family n xi epsilon C R full} := by
  ext full
  change
    (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon <
        lemma79CutoffTailMoment
          (lemma79HoldPathPointAt origin full)
          family n xi epsilon C R ↔
      (10 : ENNReal) ^ (Amarkov + 2) *
          ENNReal.ofReal (Real.exp epsilon) <
        ENNReal.ofReal
          (lemma79CutoffTailMoment
            (lemma79HoldPathPointAt origin full)
            family n xi epsilon C R)
  have hpow :
      (10 : ENNReal) ^ (Amarkov + 2) =
        ENNReal.ofReal ((10 : ℝ) ^ (Amarkov + 2)) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  rw [hpow]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]

/-- Canonical survival event with a witnessed requested endpoint strictly
inside the Case 3 window. -/
noncomputable def lemma79CanonicalSurviveWithinPEvent
    (origin : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (C R P : ℕ) : Set (List TaoSection7RenewalPoint) :=
  {full | ∃ t,
    tR? (lemma79CutoffTrace
      (lemma79HoldPathPointAt origin full) family C) R = some t ∧
      t < P}

/-- On the survival branch, a low canonical white count forces membership in
the shifted slack event.  The killed death branch is intentionally absent. -/
theorem lemma79CanonicalLowWhite_inter_surviveWithinP_subset_fSlack
    (origin : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (C R P threshold Amarkov : ℕ)
    (hroom :
      (threshold : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (R : ℝ)) :
    taoSection7Case3LowWhiteEvent
          (fun full => taoSection7Case3SourceCutoffPointW
            (lemma79HoldPathPointAt origin full) n xi epsilon C)
          P threshold ∩
        lemma79CanonicalSurviveWithinPEvent origin family C R P ⊆
      lemma79CanonicalFSlackEvent
        origin family n xi epsilon C R Amarkov := by
  intro full hfull
  rcases hfull.2 with ⟨t, ht, htP⟩
  by_contra hout
  have hnotCutoff :
      ¬ ((10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon <
        lemma79CutoffTailMoment
          (lemma79HoldPathPointAt origin full)
          family n xi epsilon C R) := by
    simpa [lemma79CanonicalFSlackEvent] using hout
  have hmomentLe :
      lemma79CutoffTailMoment
          (lemma79HoldPathPointAt origin full)
          family n xi epsilon C R ≤
        (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon :=
    le_of_not_gt hnotCutoff
  have hmomentEq :=
    lemma79CutoffTailMoment_eq_case3PositiveWhiteCount_of_tR?
      (n := n) (xi := xi) (epsilon := epsilon) ht
  rw [hmomentEq] at hmomentLe
  have hpowExp :
      (10 : ℝ) ^ (Amarkov + 2) =
        Real.exp (((Amarkov + 2 : ℕ) : ℝ) * Real.log 10) := by
    calc
      (10 : ℝ) ^ (Amarkov + 2) =
          (Real.exp (Real.log 10)) ^ (Amarkov + 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      _ = Real.exp (((Amarkov + 2 : ℕ) : ℝ) * Real.log 10) :=
        (Real.exp_nat_mul (Real.log 10) (Amarkov + 2)).symm
  have hcutoffEq :
      (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon =
        Real.exp
          (((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 + epsilon) := by
    rw [hpowExp, ← Real.exp_add]
  rw [hcutoffEq] at hmomentLe
  have hargLe := Real.exp_le_exp.mp hmomentLe
  let W : ℕ -> Prop :=
    taoSection7Case3SourceCutoffPointW
      (lemma79HoldPathPointAt origin full) n xi epsilon C
  have hthresholdReal :
      (threshold : ℝ) <
        (taoSection7Case3PositiveWhiteCount W t : ℝ) := by
    dsimp [W] at hargLe ⊢
    linarith
  have hthreshold :
      threshold < taoSection7Case3PositiveWhiteCount W t := by
    exact_mod_cast hthresholdReal
  have hpositiveLe :
      taoSection7Case3PositiveWhiteCount W t ≤
        taoSection7Case3WindowWhiteCount W P :=
    taoSection7Case3_positiveWhiteCount_le_window W htP
  have hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold := by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite, W]
      using hfull.1
  omega

/-- Countable canonical `FSlack` probability bound in the real reciprocal
form used by the Case 3 scalar ledger. -/
theorem lemma79_canonical_fSlackEvent_outerMeasure_le
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((TaoSection7Lemma77.lemma77CanonicalFirstPassageEndpointPMF
          start s).toOuterMeasure
          (TaoSection7Lemma77.lemma77CanonicalLocalizedEndpointEvent
            s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (origin : TaoSection7RenewalPoint)
    (R Amarkov Aweight : ℕ)
    (hAmarkov : Amarkov = Aweight + 1) :
    (taoSection7HoldListPMF (n / 2)).toOuterMeasure
        (lemma79CanonicalFSlackEvent origin
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          n xi epsilon (n / 2) R Amarkov) ≤
      ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3))) := by
  rw [lemma79CanonicalFSlackEvent_eq_native]
  have hnative :=
    lemma79_canonical_shiftedFSlack_outerMeasure_le
      L hlocalizedMass hxi hscalar hcollar R Amarkov Aweight
      hAmarkov origin
  calc
    _ ≤ ((10 : ENNReal) ^ (Aweight + 3))⁻¹ := hnative
    _ = ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3))) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
