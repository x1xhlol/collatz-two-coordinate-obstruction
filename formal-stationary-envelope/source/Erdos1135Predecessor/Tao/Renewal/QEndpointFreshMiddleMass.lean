/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshPairFSlack
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshPriorityPartition
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshSurvival

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79CanonicalEndpointFreshSurviveWithinPEvent
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n R P : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  {atom |
    atom.2 ∈ lemma79CanonicalSurviveWithinPEvent
      (lemma79EndpointFreshOrigin entry atom)
      family (n / 2) R P}

theorem
    lemma79CanonicalEndpointFreshLowWhite_inter_surviveWithinP_subset_fSlack
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (R P T Amarkov : ℕ)
    (hroom :
      (T : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (R : ℝ)) :
    lemma79CanonicalEndpointFreshLowWhiteEvent
          n P T xi epsilon entry ∩
        lemma79CanonicalEndpointFreshSurviveWithinPEvent
          entry family n R P ⊆
      lemma79CanonicalEndpointFreshFSlackEvent
        entry family n xi epsilon R Amarkov := by
  intro atom hatom
  have hfixed :=
    lemma79CanonicalLowWhite_inter_surviveWithinP_subset_fSlack
      (lemma79EndpointFreshOrigin entry atom)
      family n xi epsilon (n / 2) R P T Amarkov hroom
  apply hfixed
  constructor
  · simpa [lemma79CanonicalEndpointFreshLowWhiteEvent,
      lemma79CanonicalEndpointFreshCutoffW,
      lemma79EndpointFreshPointAt, lemma79EndpointFreshOrigin,
      lemma79HoldPathPointAt] using hatom.1
  · simpa [lemma79CanonicalEndpointFreshSurviveWithinPEvent] using hatom.2

theorem
    lemma79CanonicalEndpointFreshPMF_middle_outerMeasure_le_eStar_add_fSlack
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (entry : TaoSection7RenewalPoint) (gap P m T R Amarkov Aweight : ℕ)
    (hAmarkov : Amarkov = Aweight + 1)
    (hroom :
      (T : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (R : ℝ))
    (PairEStar : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint))
    (hsurvive :
      ∀ atom,
        lemma79CanonicalEndpointFreshPMF (n / 2) entry gap atom ≠ 0 →
        atom ∈
          (lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
            lemma79CanonicalEndpointFreshLowWhiteEvent
              n P T xi epsilon entry →
        atom ∉ PairEStar →
        atom ∈ lemma79CanonicalEndpointFreshSurviveWithinPEvent
          entry (taoSection7CanonicalTriangleFamily hxi hscalar)
          n R P) :
    (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap).toOuterMeasure
        ((lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
          lemma79CanonicalEndpointFreshLowWhiteEvent
            n P T xi epsilon entry) ≤
      (lemma79CanonicalEndpointFreshPMF
          (n / 2) entry gap).toOuterMeasure PairEStar +
        ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3))) := by
  let μ := lemma79CanonicalEndpointFreshPMF (n / 2) entry gap
  let Middle :=
    (lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
      lemma79CanonicalEndpointFreshLowWhiteEvent
        n P T xi epsilon entry
  let PairSurvive :=
    lemma79CanonicalEndpointFreshSurviveWithinPEvent
      entry (taoSection7CanonicalTriangleFamily hxi hscalar) n R P
  let PairFSlack :=
    lemma79CanonicalEndpointFreshFSlackEvent entry
      (taoSection7CanonicalTriangleFamily hxi hscalar)
      n xi epsilon R Amarkov
  have hsurviveFSlack :
      lemma79CanonicalEndpointFreshLowWhiteEvent
            n P T xi epsilon entry ∩ PairSurvive ⊆ PairFSlack := by
    simpa [PairSurvive, PairFSlack] using
      (lemma79CanonicalEndpointFreshLowWhite_inter_surviveWithinP_subset_fSlack
        entry (taoSection7CanonicalTriangleFamily hxi hscalar)
        n xi epsilon R P T Amarkov hroom)
  have hcover :
      ∀ atom, μ atom ≠ 0 → atom ∈ Middle →
        atom ∈ PairEStar ∪ PairFSlack := by
    intro atom hne hmiddle
    by_cases hEStar : atom ∈ PairEStar
    · exact Or.inl hEStar
    · right
      exact hsurviveFSlack
        ⟨hmiddle.2, hsurvive atom hne hmiddle hEStar⟩
  calc
    μ.toOuterMeasure Middle ≤
        μ.toOuterMeasure PairEStar + μ.toOuterMeasure PairFSlack :=
      taoSection7PMFEventMass_le_add_of_support_cover μ hcover
    _ ≤ μ.toOuterMeasure PairEStar +
        ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3))) :=
      add_le_add_right
        (lemma79CanonicalEndpointFreshPMF_fSlackEvent_outerMeasure_le
          L hlocalizedMass hxi hscalar hcollar
          entry gap R Amarkov Aweight hAmarkov) _

theorem
    lemma79CanonicalEndpointFreshPMF_middle_toReal_le_eStar_add_fSlack
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (entry : TaoSection7RenewalPoint) (gap P m T R Amarkov Aweight : ℕ)
    (hAmarkov : Amarkov = Aweight + 1)
    (hroom :
      (T : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (R : ℝ))
    (PairEStar : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint))
    (hsurvive :
      ∀ atom,
        lemma79CanonicalEndpointFreshPMF (n / 2) entry gap atom ≠ 0 →
        atom ∈
          (lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
            lemma79CanonicalEndpointFreshLowWhiteEvent
              n P T xi epsilon entry →
        atom ∉ PairEStar →
        atom ∈ lemma79CanonicalEndpointFreshSurviveWithinPEvent
          entry (taoSection7CanonicalTriangleFamily hxi hscalar)
          n R P) :
    ((lemma79CanonicalEndpointFreshPMF (n / 2) entry gap).toOuterMeasure
        ((lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
          lemma79CanonicalEndpointFreshLowWhiteEvent
            n P T xi epsilon entry)).toReal ≤
      ((lemma79CanonicalEndpointFreshPMF
          (n / 2) entry gap).toOuterMeasure PairEStar).toReal +
        1 / ((10 : ℝ) ^ (Aweight + 3)) := by
  have hnative :=
    lemma79CanonicalEndpointFreshPMF_middle_outerMeasure_le_eStar_add_fSlack
      L hlocalizedMass hxi hscalar hcollar
      entry gap P m T R Amarkov Aweight hAmarkov hroom PairEStar hsurvive
  have hEStarTop :=
    taoSection7PMFEventMass_ne_top
      (lemma79CanonicalEndpointFreshPMF (n / 2) entry gap) PairEStar
  have hrightTop : ENNReal.ofReal
      (1 / ((10 : ℝ) ^ (Aweight + 3))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  calc
    ((lemma79CanonicalEndpointFreshPMF (n / 2) entry gap).toOuterMeasure
        ((lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
          lemma79CanonicalEndpointFreshLowWhiteEvent
            n P T xi epsilon entry)).toReal ≤
      ((lemma79CanonicalEndpointFreshPMF
          (n / 2) entry gap).toOuterMeasure PairEStar +
        ENNReal.ofReal (1 / ((10 : ℝ) ^ (Aweight + 3)))).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hEStarTop, hrightTop⟩) hnative
    _ = ((lemma79CanonicalEndpointFreshPMF
          (n / 2) entry gap).toOuterMeasure PairEStar).toReal +
        1 / ((10 : ℝ) ^ (Aweight + 3)) := by
      rw [ENNReal.toReal_add hEStarTop hrightTop]
      rw [ENNReal.toReal_ofReal (by positivity)]

theorem
    lemma79CanonicalEndpointFreshPMF_middle_toReal_le_canonicalEStar_add_fSlack
    (L : ℕ)
    (hlocalizedMass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (hcollar :
      taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
        taoSection7TriangleSeparation epsilon ^ 2)
    (entry : TaoSection7RenewalPoint)
    (gap P m T R Amarkov Aweight base Kcut : ℕ)
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hP : P ≤ n / 2)
    (hR : 0 < R)
    (hiterateRoom : taoSection7Case3BaseKcutNextBoundIterateRoom
      base Kcut T (R - 1) T P)
    (hAmarkov : Amarkov = Aweight + 1)
    (hwhiteRoom :
      (T : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (R : ℝ)) :
    ((lemma79CanonicalEndpointFreshPMF (n / 2) entry gap).toOuterMeasure
        ((lemma79CanonicalEndpointFreshOuterBadJEvent P m)ᶜ ∩
          lemma79CanonicalEndpointFreshLowWhiteEvent
            n P T xi epsilon entry)).toReal ≤
      ((lemma79CanonicalEndpointFreshPMF
          (n / 2) entry gap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarEvent entry
          (taoSection7CanonicalTriangleFamily hxi hscalar)
          base Kcut T R)).toReal +
        1 / ((10 : ℝ) ^ (Aweight + 3)) := by
  apply lemma79CanonicalEndpointFreshPMF_middle_toReal_le_eStar_add_fSlack
    L hlocalizedMass hxi hscalar hcollar entry gap P m T R
      Amarkov Aweight hAmarkov hwhiteRoom
  intro atom hne hmiddle hnotEStar
  have hsurvive :=
    lemma79CanonicalEndpointFreshPMF_surviveWithinP_of_middle_not_eStar
      (taoSection7CanonicalTriangleFamily hxi hscalar)
      (taoSection7CanonicalTriangleFamily_cover hxi hscalar)
      entry gap P m T R base Kcut hboundary hP hR hiterateRoom
      hne hmiddle.1 hmiddle.2 hnotEStar
  simpa [lemma79CanonicalEndpointFreshSurviveWithinPEvent] using hsurvive

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
