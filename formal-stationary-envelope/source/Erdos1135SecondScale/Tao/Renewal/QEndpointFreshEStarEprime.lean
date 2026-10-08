/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshEStarFiber
import Erdos1135SecondScale.Tao.Renewal.Lemma710EprimeProbability

/-!
# Canonical Endpoint/Fresh EStar-Eprime Split

This leaf states Tao's fixed-offset exceptional event `E'_p` on the actual
countable endpoint/fresh carrier and partitions the corresponding EStar slice
into its inside- and outside-`E'_p` pieces.  Both pieces retain the EStar
condition; `E'_p` itself need not imply a large-triangle hit.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Tao's auxiliary exceptional event `E'_p` on the canonical
endpoint/fresh carrier.  The fresh path is truncated at the fixed offset `p`.
The three source thresholds remain explicit for later `(7.61)` input. -/
noncomputable def lemma79CanonicalEndpointFreshEprimeAt
    (entry : TaoSection7RenewalPoint)
    (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (p : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  {atom |
    EprimeSourceEvent
      (lemma77RenewalPointOfRelativeEndpoint entry atom.1)
      old horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold (atom.2.take p)}

/-- The endpoint section of `E'_p` after fixing the fresh path. -/
noncomputable def lemma79CanonicalEndpointFreshEprimeEndpointSection
    (entry : TaoSection7RenewalPoint)
    (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (p : ℕ) (fresh : List TaoSection7RenewalPoint) :
    Set (ℕ × ℤ) :=
  {endpoint |
    (endpoint, fresh) ∈
      lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold p}

/-- On a fresh list long enough to reach `p`, canonical `E'_p` membership is
exactly Tao's vertical-or-horizontal endpoint alternative. -/
theorem lemma79CanonicalEndpointFreshEprimeEndpointSection_mem_iff
    (entry : TaoSection7RenewalPoint)
    (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (p : ℕ) (fresh : List TaoSection7RenewalPoint)
    (hp : p ≤ fresh.length) (endpoint : ℕ × ℤ) :
    endpoint ∈
        lemma79CanonicalEndpointFreshEprimeEndpointSection
          entry old horizontalCenter verticalSourceThreshold
            horizontalSourceThreshold p fresh ↔
      verticalSourceThreshold ≤
          (((lemma79EndpointFreshPointAt entry (endpoint, fresh) p).l -
            old.cornerL : ℤ) : ℝ) ∨
        horizontalSourceThreshold ≤
          |(((lemma79EndpointFreshPointAt entry (endpoint, fresh) p).j : ℕ) : ℝ) -
            horizontalCenter| := by
  simp only [lemma79CanonicalEndpointFreshEprimeEndpointSection,
    lemma79CanonicalEndpointFreshEprimeAt, EprimeSourceEvent,
    EprimeVerticalSourceEvent, EprimeHorizontalSourceEvent, Set.mem_setOf_eq]
  rw [List.length_take, Nat.min_eq_left hp]
  rw [renewalPathPoint_take_eq_of_le _ _ p p le_rfl]
  rfl

/-- The part of a fixed EStar slice lying inside `E'_p`. -/
noncomputable def lemma79CanonicalEndpointFreshEStarEprimeAt
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p ∩
    lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
      verticalSourceThreshold horizontalSourceThreshold p

/-- The part of a fixed EStar slice lying outside `E'_p`. -/
noncomputable def lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p ∩
    (lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
      verticalSourceThreshold horizontalSourceThreshold p)ᶜ

/-- Exact source-valid partition of a fixed EStar slice. -/
theorem lemma79CanonicalEndpointFreshEStarAt_eq_eprime_union_outside
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p =
      lemma79CanonicalEndpointFreshEStarEprimeAt entry family old base Kcut p
        horizontalCenter verticalSourceThreshold horizontalSourceThreshold ∪
      lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
        entry family old base Kcut p horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold := by
  ext atom
  simp [lemma79CanonicalEndpointFreshEStarEprimeAt,
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt]

theorem lemma79CanonicalEndpointFreshEStarEprimeAt_disjoint_outside
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    Disjoint
      (lemma79CanonicalEndpointFreshEStarEprimeAt
        entry family old base Kcut p horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold)
      (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
        entry family old base Kcut p horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold) := by
  apply Set.disjoint_left.2
  intro atom hinside houtside
  exact houtside.2 hinside.2

theorem lemma79CanonicalEndpointFreshEStarEprimeAt_subset_eprime
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    lemma79CanonicalEndpointFreshEStarEprimeAt
        entry family old base Kcut p horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold ⊆
      lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold p := by
  intro atom hatom
  exact hatom.2

/-- Countable-carrier mass split in the source form used to combine `(7.61)`
and `(7.62)`: the inside piece is weakened to the full `E'_p` event. -/
theorem lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_eprime_add_outside
    (μ : PMF ((ℕ × ℤ) × List TaoSection7RenewalPoint))
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarAt entry family base Kcut p) ≤
      μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold p) +
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold) := by
  rw [lemma79CanonicalEndpointFreshEStarAt_eq_eprime_union_outside]
  calc
    μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarEprimeAt
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold ∪
          lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold) ≤
      μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarEprimeAt
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold) +
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold) :=
        MeasureTheory.measure_union_le _ _
    _ ≤ _ := add_le_add_left
      (μ.toOuterMeasure.mono
        (lemma79CanonicalEndpointFreshEStarEprimeAt_subset_eprime
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold)) _

/-- Safe-real projection of the fixed-offset `(7.61)`/`(7.62)` mass split. -/
theorem lemma79CanonicalEndpointFreshEStarAt_toReal_le_eprime_add_outside
    (μ : PMF ((ℕ × ℤ) × List TaoSection7RenewalPoint))
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ) :
    (μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarAt
          entry family base Kcut p)).toReal ≤
      (μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold p)).toReal +
      (μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold)).toReal := by
  have hnative :=
    lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_eprime_add_outside
      μ entry family old base Kcut p horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold
  have hleft := taoSection7PMFEventMass_ne_top μ
    (lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
      verticalSourceThreshold horizontalSourceThreshold p)
  have hright := taoSection7PMFEventMass_ne_top μ
    (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
      entry family old base Kcut p horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold)
  have hsum :
      μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEprimeAt entry old horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold p) +
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hleft, hright⟩
  have hreal := ENNReal.toReal_mono hsum hnative
  rw [ENNReal.toReal_add hleft hright] at hreal
  exact hreal

/-- The outside-`E'_p` endpoint section obtained after fixing the fresh path. -/
noncomputable def
    lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (fresh : List TaoSection7RenewalPoint) : Set (ℕ × ℤ) :=
  lemma79CanonicalEndpointFreshEStarEndpointSection
      entry family base Kcut p fresh ∩
    (lemma79CanonicalEndpointFreshEprimeEndpointSection
      entry old horizontalCenter verticalSourceThreshold
        horizontalSourceThreshold p fresh)ᶜ

/-- Exact fixed-fresh endpoint-section partition. -/
theorem
    lemma79CanonicalEndpointFreshEStarEndpointSection_eq_eprime_union_outside
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (fresh : List TaoSection7RenewalPoint) :
    lemma79CanonicalEndpointFreshEStarEndpointSection
        entry family base Kcut p fresh =
      (lemma79CanonicalEndpointFreshEStarEndpointSection
          entry family base Kcut p fresh ∩
        lemma79CanonicalEndpointFreshEprimeEndpointSection
          entry old horizontalCenter verticalSourceThreshold
            horizontalSourceThreshold p fresh) ∪
      lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
        entry family old base Kcut p horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold fresh := by
  ext endpoint
  simp [lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection]

/-- Native endpoint-PMF mass split after fixing the fresh path.  The inside
intersection is weakened to the full endpoint `E'_p` section, matching the
separate exceptional-event estimate `(7.61)`. -/
theorem
    lemma79CanonicalEndpointFreshEStarEndpointSection_outerMeasure_le_eprime_add_outside
    (μ : PMF (ℕ × ℤ))
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (fresh : List TaoSection7RenewalPoint) :
    μ.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarEndpointSection
          entry family base Kcut p fresh) ≤
      μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEprimeEndpointSection
            entry old horizontalCenter verticalSourceThreshold
              horizontalSourceThreshold p fresh) +
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold fresh) := by
  rw [lemma79CanonicalEndpointFreshEStarEndpointSection_eq_eprime_union_outside]
  calc
    μ.toOuterMeasure
        ((lemma79CanonicalEndpointFreshEStarEndpointSection
            entry family base Kcut p fresh ∩
          lemma79CanonicalEndpointFreshEprimeEndpointSection
            entry old horizontalCenter verticalSourceThreshold
              horizontalSourceThreshold p fresh) ∪
          lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold fresh) ≤
      μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarEndpointSection
            entry family base Kcut p fresh ∩
          lemma79CanonicalEndpointFreshEprimeEndpointSection
            entry old horizontalCenter verticalSourceThreshold
              horizontalSourceThreshold p fresh) +
        μ.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
            entry family old base Kcut p horizontalCenter
              verticalSourceThreshold horizontalSourceThreshold fresh) :=
        MeasureTheory.measure_union_le _ _
    _ ≤ _ := add_le_add_left
      (μ.toOuterMeasure.mono (Set.inter_subset_right)) _

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end
end Tao
end Erdos1135SecondScale
