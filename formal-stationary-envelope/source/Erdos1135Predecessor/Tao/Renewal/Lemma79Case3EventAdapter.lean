/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79NativeMarkov

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

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

noncomputable def lemma79CanonicalSurviveWithinPEvent
    (origin : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (C R P : ℕ) : Set (List TaoSection7RenewalPoint) :=
  {full | ∃ t,
    tR? (lemma79CutoffTrace
      (lemma79HoldPathPointAt origin full) family C) R = some t ∧
      t < P}

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
