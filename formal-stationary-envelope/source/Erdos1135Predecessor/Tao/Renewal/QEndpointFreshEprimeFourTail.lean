/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.Lemma79EndpointFreshCoordinates
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarEprime
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshMarginals
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshSupport

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

def lemma79CanonicalFreshVerticalTailEvent
    (entry : TaoSection7RenewalPoint) (p X : ℕ) :
    Set (List TaoSection7RenewalPoint) :=
  {fresh |
    (X : ℤ) ≤ lemma77HoldPrefixVerticalIncrement entry p fresh}

noncomputable def lemma79CanonicalFreshHorizontalTailEvent
    (p : ℕ) (t : ℝ) :
    Set (List TaoSection7RenewalPoint) :=
  {fresh |
    t ≤ (lemma77HoldPrefixHorizontalDelta p fresh : ℝ)}

def lemma79CanonicalEprimeVerticalEndpointEvent
    (fpGap X : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  Prod.fst ⁻¹' lemma77CanonicalVerticalOvershootTailEvent fpGap X

def lemma79CanonicalEprimeFreshVerticalEvent
    (entry : TaoSection7RenewalPoint) (p X : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (fun atom => atom.2.take p) ⁻¹'
    lemma79CanonicalFreshVerticalTailEvent entry p X

noncomputable def lemma79CanonicalEprimeHorizontalEndpointEvent
    (fpGap : ℕ) (t : ℝ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (fun atom => atom.1.1) ⁻¹'
    lemma77CanonicalHorizontalDeviationEvent fpGap t

noncomputable def lemma79CanonicalEprimeFreshHorizontalEvent
    (p : ℕ) (t : ℝ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (fun atom => atom.2.take p) ⁻¹'
    lemma79CanonicalFreshHorizontalTailEvent p t

theorem lemma79HoldPrefixVerticalIncrement_take
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (fresh : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixVerticalIncrement start p (fresh.take p) =
      lemma77HoldPrefixVerticalIncrement start p fresh := by
  induction p generalizing start fresh with
  | zero =>
      simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
  | succ p ih =>
      cases fresh with
      | nil =>
          simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
      | cons h fresh =>
          have hih := ih (start + h) fresh
          simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement,
            taoSection7RenewalPathPoint] at hih ⊢
          omega

theorem lemma79EndpointFresh_verticalOffset_eq
    (entry : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (fpGap p : ℕ) (endpoint : ℕ × ℤ)
    (fresh : List TaoSection7RenewalPoint)
    (hgap : old.cornerL - entry.l = (fpGap : ℤ)) :
    (((lemma79EndpointFreshPointAt entry (endpoint, fresh) p).l -
        old.cornerL : ℤ) : ℝ) =
      (((endpoint.2 - (fpGap : ℤ) : ℤ) : ℝ) +
        (lemma77HoldPrefixVerticalIncrement entry p fresh : ℝ)) := by
  change
    (((taoSection7RenewalPathPoint
          (lemma77RenewalPointOfRelativeEndpoint entry endpoint) fresh p).l -
        old.cornerL : ℤ) : ℝ) = _
  rw [lemma79EndpointFresh_pathPoint_eq_relativeEndpoint]
  simp only [lemma77RenewalPointOfRelativeEndpoint_l]
  rw [← Int.cast_add]
  apply congrArg (fun z : ℤ => (z : ℝ))
  omega

theorem lemma79EndpointFresh_horizontalOffset_eq
    (entry : TaoSection7RenewalPoint) (horizontalCenter : ℝ)
    (fpGap p : ℕ) (endpoint : ℕ × ℤ)
    (fresh : List TaoSection7RenewalPoint)
    (hcenter :
      horizontalCenter = entry.toPoint.jReal + (fpGap : ℝ) / 4) :
    (((lemma79EndpointFreshPointAt entry (endpoint, fresh) p).j : ℕ) : ℝ) -
        horizontalCenter =
      lemma77CenteredHorizontalDisplacement fpGap endpoint.1 +
        (lemma77HoldPrefixHorizontalDelta p fresh : ℝ) := by
  change
    (((taoSection7RenewalPathPoint
          (lemma77RenewalPointOfRelativeEndpoint entry endpoint) fresh p).j :
        ℕ) : ℝ) - horizontalCenter = _
  rw [lemma79EndpointFresh_pathPoint_eq_relativeEndpoint]
  simp only [lemma77RenewalPointOfRelativeEndpoint_j]
  rw [hcenter]
  simp only [TaoSection7Point.jReal, TaoSection7RenewalPoint.toPoint_j]
  unfold lemma77CenteredHorizontalDisplacement
  push_cast
  ring

theorem lemma79CanonicalEndpointFreshEprimeAt_mem_fourTail_of_support
    {J p fpGap X : ℕ}
    {entry : TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {horizontalCenter t : ℝ}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hpJ : p ≤ J)
    (hne : lemma79CanonicalEndpointFreshPMF J entry fpGap atom ≠ 0)
    (hgap : old.cornerL - entry.l = (fpGap : ℤ))
    (hcenter :
      horizontalCenter = entry.toPoint.jReal + (fpGap : ℝ) / 4)
    (hEprime :
      atom ∈ lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
        (2 * (X : ℝ)) (2 * t) p) :
    atom ∈
        lemma79CanonicalEprimeVerticalEndpointEvent fpGap X ∪
          (lemma79CanonicalEprimeFreshVerticalEvent entry p X ∪
            (lemma79CanonicalEprimeHorizontalEndpointEvent fpGap t ∪
              lemma79CanonicalEprimeFreshHorizontalEvent p t)) := by
  rcases atom with ⟨endpoint, fresh⟩
  have hpLen : p ≤ fresh.length :=
    (lemma79CanonicalEndpointFreshPMF_used_fresh_support hpJ hne).1
  have hbounds :
      2 * (X : ℝ) ≤
          (((lemma79EndpointFreshPointAt entry (endpoint, fresh) p).l -
            old.cornerL : ℤ) : ℝ) ∨
        2 * t ≤
          |(((lemma79EndpointFreshPointAt entry (endpoint, fresh) p).j : ℕ) :
              ℝ) - horizontalCenter| := by
    exact
      (lemma79CanonicalEndpointFreshEprimeEndpointSection_mem_iff
        entry old horizontalCenter (2 * (X : ℝ)) (2 * t)
          p fresh hpLen endpoint).1 hEprime
  rw [lemma79EndpointFresh_verticalOffset_eq
      entry old fpGap p endpoint fresh hgap,
    lemma79EndpointFresh_horizontalOffset_eq
      entry horizontalCenter fpGap p endpoint fresh hcenter] at hbounds
  change
    (fpGap : ℤ) + (X : ℤ) ≤ endpoint.2 ∨
      (X : ℤ) ≤
          lemma77HoldPrefixVerticalIncrement entry p (fresh.take p) ∨
        t ≤ |lemma77CenteredHorizontalDisplacement fpGap endpoint.1| ∨
          t ≤
            (lemma77HoldPrefixHorizontalDelta p (fresh.take p) : ℝ)
  rw [lemma79HoldPrefixVerticalIncrement_take,
    lemma79HoldPrefixHorizontalDelta_take]
  rcases hbounds with hvertical | hhorizontal
  · by_cases hpre : (fpGap : ℤ) + (X : ℤ) ≤ endpoint.2
    · exact Or.inl hpre
    by_cases hfresh :
        (X : ℤ) ≤ lemma77HoldPrefixVerticalIncrement entry p fresh
    · exact Or.inr (Or.inl hfresh)
    · have hpreReal :
          (((endpoint.2 - (fpGap : ℤ) : ℤ) : ℝ)) < (X : ℝ) := by
        exact_mod_cast (show endpoint.2 - (fpGap : ℤ) < (X : ℤ) by omega)
      have hfreshReal :
          (lemma77HoldPrefixVerticalIncrement entry p fresh : ℝ) <
            (X : ℝ) := by
        exact_mod_cast
          (show lemma77HoldPrefixVerticalIncrement entry p fresh <
              (X : ℤ) by omega)
      exfalso
      nlinarith
  · by_cases hpre :
        t ≤ |lemma77CenteredHorizontalDisplacement fpGap endpoint.1|
    · exact Or.inr (Or.inr (Or.inl hpre))
    by_cases hfresh :
        t ≤ (lemma77HoldPrefixHorizontalDelta p fresh : ℝ)
    · exact Or.inr (Or.inr (Or.inr hfresh))
    · have hpre' := lt_of_not_ge hpre
      have hfresh' := lt_of_not_ge hfresh
      have hnonneg :
          0 ≤ (lemma77HoldPrefixHorizontalDelta p fresh : ℝ) :=
        Nat.cast_nonneg _
      have htriangle :
          |lemma77CenteredHorizontalDisplacement fpGap endpoint.1 +
              (lemma77HoldPrefixHorizontalDelta p fresh : ℝ)| ≤
            |lemma77CenteredHorizontalDisplacement fpGap endpoint.1| +
              (lemma77HoldPrefixHorizontalDelta p fresh : ℝ) := by
        simpa [abs_of_nonneg hnonneg] using
          (abs_add_le
            (lemma77CenteredHorizontalDisplacement fpGap endpoint.1)
            (lemma77HoldPrefixHorizontalDelta p fresh : ℝ))
      exfalso
      nlinarith

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
