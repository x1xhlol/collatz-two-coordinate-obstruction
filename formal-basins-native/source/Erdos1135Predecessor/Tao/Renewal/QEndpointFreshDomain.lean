/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79EndpointFreshLaw
import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstEntryCount
import Erdos1135Predecessor.Tao.Renewal.Outer754HorizontalFactor
import Erdos1135Predecessor.Tao.Renewal.Prop78Boundary
import Erdos1135Predecessor.Tao.Renewal.QmHorizontalNormalization

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

def lemma79EndpointFreshOrigin
    (entry : TaoSection7RenewalPoint)
    (atom : (ℕ × ℤ) × List TaoSection7RenewalPoint) :
    TaoSection7RenewalPoint :=
  lemma77RenewalPointOfRelativeEndpoint entry atom.1

def lemma79EndpointFreshHorizontalAdvance
    (P : ℕ) (atom : (ℕ × ℤ) × List TaoSection7RenewalPoint) : ℕ :=
  atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2

def lemma79EndpointFreshPointAt
    (entry : TaoSection7RenewalPoint)
    (atom : (ℕ × ℤ) × List TaoSection7RenewalPoint)
    (p : ℕ) : TaoSection7Point :=
  (taoSection7RenewalPathPoint
    (lemma79EndpointFreshOrigin entry atom) atom.2 p).toPoint

theorem lemma79CanonicalEndpointFreshPMF_actualQ_at_le_normalized
    {n A m P J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 <= epsilon) (hm : 1 <= m)
    {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hne : lemma79CanonicalEndpointFreshPMF J entry gap atom ≠ 0) :
    taoSection7SourceActualQ n xi epsilon
        (taoSection7RenewalPathPoint
          (lemma79EndpointFreshOrigin entry atom) atom.2 P) <=
      ((m : ℝ) ^ A)⁻¹ *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon *
        taoSection7Case3Outer754HorizontalFactor A m
          (lemma79EndpointFreshHorizontalAdvance P) atom := by
  let endpointAt :
      ((ℕ × ℤ) × List TaoSection7RenewalPoint) ->
        TaoSection7RenewalPoint :=
    fun z => taoSection7RenewalPathPoint
      (lemma79EndpointFreshOrigin entry z) z.2 P
  have hJtot : 1 <= lemma79EndpointFreshHorizontalAdvance P atom :=
    lemma79CanonicalEndpointFreshPMF_horizontalAdvance_pos hne
  have hendpoint_j :
      ((endpointAt atom).j : ℕ) =
        (entry.j : ℕ) + lemma79EndpointFreshHorizontalAdvance P atom := by
    rw [lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]
    simp [lemma79EndpointFreshOrigin,
      lemma79EndpointFreshHorizontalAdvance]
    omega
  simpa [endpointAt] using
    (taoSection7SourceActualQ_horizontalAdvance_le_normalized
      (Omega := (ℕ × ℤ) × List TaoSection7RenewalPoint)
      hepsilon hm hboundary endpointAt
      (lemma79EndpointFreshHorizontalAdvance P) atom hJtot hendpoint_j)

theorem lemma79EndpointFreshPrefix_sourceDomain_of_not_largeHorizontal
    {n m P Jtot : ℕ}
    {entry : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hnotLarge : ¬ 9 * m <= 10 * Jtot)
    (endpoint : ℕ × ℤ)
    (fresh : List TaoSection7RenewalPoint)
    (hprefix :
      ∀ p, p <= P ->
        endpoint.1 + lemma77HoldPrefixHorizontalDelta p fresh <= Jtot) :
    ∀ p, p <= P ->
      taoSection7SourcePointInDomain (n / 2)
        (taoSection7RenewalPathPoint
          (lemma77RenewalPointOfRelativeEndpoint entry endpoint)
          fresh p).toPoint := by
  intro p hp
  have hJtot_lt_m : Jtot < m := by omega
  have hprefix_p := hprefix p hp
  unfold taoSection7SourcePointInDomain
  change
    ((taoSection7RenewalPathPoint
      (lemma77RenewalPointOfRelativeEndpoint entry endpoint)
      fresh p).j : ℕ) <= n / 2
  rw [lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]
  rw [lemma77RenewalPointOfRelativeEndpoint_j]
  unfold taoSection7QmBoundary at hboundary
  omega

theorem lemma79CanonicalEndpointFreshPMF_sourceDomain_of_not_largeHorizontal
    {n m P J : ℕ}
    {entry : TaoSection7RenewalPoint} {gap : ℕ}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hPJ : P <= J)
    (hne : lemma79CanonicalEndpointFreshPMF J entry gap atom ≠ 0)
    (hnotLarge :
      atom ∉ taoSection7Case3Outer754LargeHorizontalEvent
        (lemma79EndpointFreshHorizontalAdvance P) m) :
    P <= atom.2.length ∧
      ∀ p, p <= P ->
        taoSection7SourcePointInDomain (n / 2)
          (lemma79EndpointFreshPointAt entry atom p) := by
  have hlength :=
    (lemma79CanonicalEndpointFreshPMF_nonzero_support hne).2.2
  have hP_length : P <= atom.2.length := by omega
  have hnot :
      ¬ 9 * m <=
        10 * lemma79EndpointFreshHorizontalAdvance P atom := by
    simpa [taoSection7Case3Outer754LargeHorizontalEvent] using hnotLarge
  have hprefix : ∀ p, p <= P ->
      atom.1.1 + lemma77HoldPrefixHorizontalDelta p atom.2 <=
        lemma79EndpointFreshHorizontalAdvance P atom := by
    intro p hp
    have hmono := lemma79HoldPathPoint_j_mono
      (lemma79EndpointFreshOrigin entry atom) atom.2 hp
    change
      ((taoSection7RenewalPathPoint
        (lemma79EndpointFreshOrigin entry atom) atom.2 p).j : ℕ) <=
      ((taoSection7RenewalPathPoint
        (lemma79EndpointFreshOrigin entry atom) atom.2 P).j : ℕ) at hmono
    rw [lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta,
      lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta] at hmono
    simp only [lemma79EndpointFreshOrigin,
      lemma77RenewalPointOfRelativeEndpoint_j] at hmono
    simpa [lemma79EndpointFreshHorizontalAdvance] using hmono
  refine ⟨hP_length, ?_⟩
  simpa [lemma79EndpointFreshPointAt, lemma79EndpointFreshOrigin] using
    (lemma79EndpointFreshPrefix_sourceDomain_of_not_largeHorizontal
      hboundary hnot atom.1 atom.2 hprefix)

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
