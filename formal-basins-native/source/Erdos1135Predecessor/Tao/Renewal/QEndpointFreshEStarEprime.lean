/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma710EprimeProbability
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarFiber

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
