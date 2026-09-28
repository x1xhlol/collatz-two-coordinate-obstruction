/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma710KernelWindow
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeNearSigma

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

def lemma79EndpointFreshHorizontalShift
    (entry : TaoSection7RenewalPoint) (p : ℕ)
    (fresh : List TaoSection7RenewalPoint) : ℤ :=
  ((entry.j : ℕ) : ℤ) +
    (lemma77HoldPrefixHorizontalDelta p fresh : ℤ)

noncomputable def lemma79EndpointFreshNearSigmaHorizontalEvent
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (sMin K B : ℝ) (p R : ℕ)
    (fresh : List TaoSection7RenewalPoint) : Set ℕ :=
  {r |
    ∃ q : TaoSection7Point,
      q ∈ Sigma family old sMin K B ∧
        (r : ℤ) + lemma79EndpointFreshHorizontalShift entry p fresh ∈
          taoSection7IntIccWindow R (((q.j : ℕ) : ℤ))}

theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_mem_iff_endpointSection
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold : ℝ)
    (endpoint : ℕ × ℤ) (fresh : List TaoSection7RenewalPoint) :
    (endpoint, fresh) ∈
        lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold ↔
      endpoint ∈
        lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh := by
  simp only [lemma79CanonicalEndpointFreshEStarOutsideEprimeAt,
    lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection,
    Set.mem_inter_iff, Set.mem_compl_iff]
  rw [lemma79CanonicalEndpointFreshEStarAt_mem_iff_endpointSection]
  rfl

theorem lemma79EndpointFreshNearSigmaHorizontalEvent_mem_of_nearSigma
    {entry : TaoSection7RenewalPoint}
    {endpoint : ℕ × ℤ} {fresh : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {sMin K B : ℝ} {p R : ℕ}
    (hnear :
      NearSigma (R : ℝ) (Sigma family old sMin K B)
        (lemma79EndpointFreshPointAt entry (endpoint, fresh) p)) :
    endpoint.1 ∈
      lemma79EndpointFreshNearSigmaHorizontalEvent
        entry family old sMin K B p R fresh := by
  rcases hnear with ⟨q, hq, hdist⟩
  refine ⟨q, hq, ?_⟩
  have hj := j_mem_intWindow_of_distSq_le hdist
  simpa [lemma79EndpointFreshPointAt, lemma79EndpointFreshOrigin,
    lemma79EndpointFreshHorizontalShift,
    lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta,
    lemma77RenewalPointOfRelativeEndpoint_j, add_assoc, add_comm,
    add_left_comm] using hj

theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection_outerMeasure_le_horizontalNearSigma
    {fpGap base Kcut p R : ℕ}
    {entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin K B : ℝ}
    (fresh : List TaoSection7RenewalPoint)
    (hnear : ∀ endpoint,
      lemma77CanonicalFirstPassageEndpointPMF entry fpGap endpoint ≠ 0 →
      endpoint ∈
        lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh →
      NearSigma (R : ℝ) (Sigma family old sMin K B)
        (lemma79EndpointFreshPointAt entry (endpoint, fresh) p)) :
    (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh) ≤
      (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) := by
  calc
    (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh) ≤
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        {endpoint |
          endpoint.1 ∈ lemma79EndpointFreshNearSigmaHorizontalEvent
            entry family old sMin K B p R fresh} := by
      apply (lemma77CanonicalFirstPassageEndpointPMF
        entry fpGap).toOuterMeasure_mono
      rintro endpoint ⟨hsection, hsupport⟩
      exact lemma79EndpointFreshNearSigmaHorizontalEvent_mem_of_nearSigma
        (hnear endpoint hsupport hsection)
    _ = (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) := by
      change
        (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
            (Prod.fst ⁻¹' lemma79EndpointFreshNearSigmaHorizontalEvent
              entry family old sMin K B p R fresh) =
          ((lemma77CanonicalFirstPassageEndpointPMF entry fpGap).map
            Prod.fst).toOuterMeasure
              (lemma79EndpointFreshNearSigmaHorizontalEvent
                entry family old sMin K B p R fresh)
      rw [PMF.toOuterMeasure_map_apply]

theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection_outerMeasure_le_horizontalEvent
    {J fpGap base Kcut p R : ℕ}
    {entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin S Lerr Jerr gap K B Jgeo : ℝ}
    (fresh : List TaoSection7RenewalPoint)
    (hfresh : fresh ∈ (taoSection7HoldListPMF J).support)
    (hpJ : p ≤ J)
    (hgapAlign : old.cornerL - entry.l = (fpGap : ℤ))
    (hbase : old.Mem entry.toPoint)
    (hS : S = ((old.cornerL - entry.toPoint.l : ℤ) : ℝ))
    (hcenter : horizontalCenter = entry.toPoint.jReal + S / 4)
    (hV : verticalSourceThreshold ≤ Lerr)
    (hJerr : horizontalSourceThreshold ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hL0 : 0 ≤ Lerr)
    (hJ0 : 0 ≤ Jerr)
    (hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family)
    (hsize :
      sMin ≤ taoSection7Case3LargeTriangleBoundWithBase
        (base : ℝ) Kcut p)
    (hJgeo : (Real.log 2 / Real.log 9) * (K * B + K * B) ≤ Jgeo)
    (hradius : Jgeo ^ 2 + (K * B) ^ 2 ≤ (R : ℝ) ^ 2)
    (hgapKB : gap ≤ K * B)
    (hLerrKB : Lerr ≤ K * B) :
    (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh) ≤
      (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) := by
  apply
    lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection_outerMeasure_le_horizontalNearSigma
  intro endpoint hendpoint hsection
  have hjoint :
      lemma79CanonicalEndpointFreshPMF J entry fpGap
          (endpoint, fresh) ≠ 0 := by
    rw [lemma79CanonicalEndpointFreshPMF_apply]
    exact mul_ne_zero hendpoint hfresh
  have hatom :
      (endpoint, fresh) ∈
        lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold :=
    (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_mem_iff_endpointSection
      entry family old base Kcut p horizontalCenter
        verticalSourceThreshold horizontalSourceThreshold endpoint fresh).2
      hsection
  rcases
      lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_to_center_nearSigma
        hpJ hjoint hgapAlign hatom hbase hS hcenter hV hJerr hgap0 hL0 hJ0
          hmargin hpair hold hsize hJgeo hradius hgapKB hLerrKB with
    ⟨c, hc⟩
  exact hc

theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_of_fresh_fibers
    (J : ℕ) (entry : TaoSection7RenewalPoint) (fpGap : ℕ)
    (family : Set TaoSection7Triangle) (old : TaoSection7Triangle)
    (base Kcut p : ℕ)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ)
    (Bbound : ENNReal)
    (hfiber : ∀ fresh ∈ (taoSection7HoldListPMF J).support,
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh) ≤ Bbound) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold) ≤ Bbound := by
  apply taoSection7PMFBindPair_eventMass_le_of_fiber
  intro fresh hfresh
  calc
    (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        {endpoint |
          (endpoint, fresh) ∈
            lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
              entry family old base Kcut p horizontalCenter
                verticalSourceThreshold horizontalSourceThreshold} =
      (lemma77CanonicalFirstPassageEndpointPMF entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold fresh) := by
      congr 1
      ext endpoint
      exact
        lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_mem_iff_endpointSection
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold endpoint fresh
    _ ≤ Bbound := hfiber fresh hfresh

theorem
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_of_horizontalEvents
    {J fpGap base Kcut p R : ℕ}
    {entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold horizontalSourceThreshold
      sMin S Lerr Jerr gap K B Jgeo : ℝ}
    {Bbound : ENNReal}
    (hpJ : p ≤ J)
    (hgapAlign : old.cornerL - entry.l = (fpGap : ℤ))
    (hbase : old.Mem entry.toPoint)
    (hS : S = ((old.cornerL - entry.toPoint.l : ℤ) : ℝ))
    (hcenter : horizontalCenter = entry.toPoint.jReal + S / 4)
    (hV : verticalSourceThreshold ≤ Lerr)
    (hJerr : horizontalSourceThreshold ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hL0 : 0 ≤ Lerr)
    (hJ0 : 0 ≤ Jerr)
    (hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family)
    (hsize :
      sMin ≤ taoSection7Case3LargeTriangleBoundWithBase
        (base : ℝ) Kcut p)
    (hJgeo : (Real.log 2 / Real.log 9) * (K * B + K * B) ≤ Jgeo)
    (hradius : Jgeo ^ 2 + (K * B) ^ 2 ≤ (R : ℝ) ^ 2)
    (hgapKB : gap ≤ K * B)
    (hLerrKB : Lerr ≤ K * B)
    (hbound : ∀ fresh ∈ (taoSection7HoldListPMF J).support,
      (lemma77CanonicalFirstPassageHorizontalPMF entry fpGap).toOuterMeasure
        (lemma79EndpointFreshNearSigmaHorizontalEvent
          entry family old sMin K B p R fresh) ≤ Bbound) :
    (lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
          entry family old base Kcut p horizontalCenter
            verticalSourceThreshold horizontalSourceThreshold) ≤ Bbound := by
  apply
    lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_outerMeasure_le_of_fresh_fibers
  intro fresh hfresh
  exact
    (lemma79CanonicalEndpointFreshEStarOutsideEprimeEndpointSection_outerMeasure_le_horizontalEvent
      fresh hfresh hpJ hgapAlign hbase hS hcenter hV hJerr hgap0 hL0 hJ0
        hmargin hpair hold hsize hJgeo hradius hgapKB hLerrKB).trans
      (hbound fresh hfresh)

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
