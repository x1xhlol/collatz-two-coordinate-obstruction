import Erdos1135.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135.Tao.Renewal.Lemma79EndpointFreshCoordinates
import Erdos1135.Tao.Renewal.QEndpointFreshEStarEprime
import Erdos1135.Tao.Renewal.QEndpointFreshMarginals
import Erdos1135.Tao.Renewal.QEndpointFreshSupport

/-!
# Canonical Endpoint/Fresh Four-Tail Cover

This proof leaf splits Tao's auxiliary exceptional event `E'_p` into the
first-passage and fresh vertical and horizontal tails from `(7.61)`.  The
cover is support-wise because an arbitrary fresh list need not reach time
`p`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The fresh vertical tail at time `p`, retaining the signed increment. -/
def lemma79CanonicalFreshVerticalTailEvent
    (entry : TaoSection7RenewalPoint) (p X : ℕ) :
    Set (List TaoSection7RenewalPoint) :=
  {fresh |
    (X : ℤ) ≤ lemma77HoldPrefixVerticalIncrement entry p fresh}

/-- The fresh horizontal tail at time `p` with its literal real threshold. -/
noncomputable def lemma79CanonicalFreshHorizontalTailEvent
    (p : ℕ) (t : ℝ) :
    Set (List TaoSection7RenewalPoint) :=
  {fresh |
    t ≤ (lemma77HoldPrefixHorizontalDelta p fresh : ℝ)}

/-- The first-passage vertical tail lifted to the endpoint/fresh carrier. -/
def lemma79CanonicalEprimeVerticalEndpointEvent
    (fpGap X : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  Prod.fst ⁻¹' lemma77CanonicalVerticalOvershootTailEvent fpGap X

/-- The fresh vertical tail lifted through the canonical `p`-prefix map. -/
def lemma79CanonicalEprimeFreshVerticalEvent
    (entry : TaoSection7RenewalPoint) (p X : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (fun atom => atom.2.take p) ⁻¹'
    lemma79CanonicalFreshVerticalTailEvent entry p X

/-- The first-passage horizontal tail lifted to the endpoint/fresh carrier. -/
noncomputable def lemma79CanonicalEprimeHorizontalEndpointEvent
    (fpGap : ℕ) (t : ℝ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (fun atom => atom.1.1) ⁻¹'
    lemma77CanonicalHorizontalDeviationEvent fpGap t

/-- The fresh horizontal tail lifted through the canonical `p`-prefix map. -/
noncomputable def lemma79CanonicalEprimeFreshHorizontalEvent
    (p : ℕ) (t : ℝ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  (fun atom => atom.2.take p) ⁻¹'
    lemma79CanonicalFreshHorizontalTailEvent p t

/-- Signed vertical displacement depends only on the corresponding prefix. -/
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

/-- Corner-gap alignment identifies the final signed vertical displacement
with the first-passage overshoot plus the fresh vertical increment. -/
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

/-- Center alignment identifies the final horizontal displacement with the
centered first-passage displacement plus the fresh horizontal increment. -/
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

/-- On every nonzero canonical atom, `E'_p(2X,2t)` is covered by Tao's four
inclusive tails: first-passage vertical, fresh vertical, first-passage
horizontal, and fresh horizontal. -/
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
end Erdos1135
