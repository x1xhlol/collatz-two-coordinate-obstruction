import Erdos1135.Tao.Renewal.QEndpointFreshEStarEprime
import Erdos1135.Tao.Renewal.QEndpointFreshSupport

/-!
# Canonical Outside-Eprime Near-Sigma Bridge

This proof leaf sends a supported canonical endpoint/fresh atom in the
outside-`E'_p` part of `EStar` directly through the deterministic Lemma 7.10
geometry.  It deliberately avoids reconstructing a source clock: canonical
first-passage support supplies the missing strict lower endpoint estimate.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77
open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A supported canonical outside-`E'_p` atom lies near a center of a distinct
large triangle.  All scale absorptions used by the deterministic geometry
remain explicit. -/
theorem lemma79CanonicalEndpointFreshEStarOutsideEprimeAt_to_center_nearSigma
    {J eventBase Kcut p fpGap : ℕ}
    {entry : TaoSection7RenewalPoint}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold
      horizontalSourceThreshold sMin S Lerr Jerr gap K B Jgeo R : ℝ}
    (hpJ : p ≤ J)
    (hne : lemma79CanonicalEndpointFreshPMF J entry fpGap atom ≠ 0)
    (hgapAlign : old.cornerL - entry.l = (fpGap : ℤ))
    (hatom : atom ∈
      lemma79CanonicalEndpointFreshEStarOutsideEprimeAt
        entry family old eventBase Kcut p horizontalCenter
          verticalSourceThreshold horizontalSourceThreshold)
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
        (eventBase : ℝ) Kcut p)
    (hJgeo : (Real.log 2 / Real.log 9) * (K * B + K * B) ≤ Jgeo)
    (hradius : Jgeo ^ 2 + (K * B) ^ 2 ≤ R ^ 2)
    (hgapKB : gap ≤ K * B)
    (hLerrKB : Lerr ≤ K * B) :
    ∃ c : Center family old sMin K B,
      NearSigma R (Sigma family old sMin K B)
        (lemma79EndpointFreshPointAt entry atom p) := by
  rcases hatom with
    ⟨⟨new, hnew_family, hnew_mem, hnew_size⟩, hnotEprime⟩
  have hpLen : p ≤ atom.2.length :=
    (lemma79CanonicalEndpointFreshPMF_used_fresh_support hpJ hne).1
  have hnotEndpoint :
      atom.1 ∉ lemma79CanonicalEndpointFreshEprimeEndpointSection
        entry old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold p atom.2 := by
    exact hnotEprime
  have hnotBounds :
      ¬ (verticalSourceThreshold ≤
          (((lemma79EndpointFreshPointAt entry atom p).l -
            old.cornerL : ℤ) : ℝ) ∨
        horizontalSourceThreshold ≤
          |(((lemma79EndpointFreshPointAt entry atom p).j : ℕ) : ℝ) -
            horizontalCenter|) := by
    intro hbounds
    exact hnotEndpoint
      ((lemma79CanonicalEndpointFreshEprimeEndpointSection_mem_iff
        entry old horizontalCenter verticalSourceThreshold
          horizontalSourceThreshold p atom.2 hpLen atom.1).2 hbounds)
  have hlowerInt :
      old.cornerL < (lemma79EndpointFreshPointAt entry atom p).l :=
    lemma79CanonicalEndpointFreshPMF_cornerL_lt_pointAt
      hne hpJ hgapAlign
  have hlower :
      (old.cornerL : ℝ) ≤
        (lemma79EndpointFreshPointAt entry atom p).lReal := by
    change (old.cornerL : ℝ) ≤
      ((lemma79EndpointFreshPointAt entry atom p).l : ℝ)
    exact_mod_cast hlowerInt.le
  have hupper :
      (lemma79EndpointFreshPointAt entry atom p).lReal -
          (old.cornerL : ℝ) ≤ Lerr := by
    have hlt :
        (((lemma79EndpointFreshPointAt entry atom p).l -
          old.cornerL : ℤ) : ℝ) < verticalSourceThreshold := by
      exact lt_of_not_ge (fun h => hnotBounds (Or.inl h))
    exact le_trans (by simpa [TaoSection7Point.lReal] using hlt.le) hV
  have hj :
      |(lemma79EndpointFreshPointAt entry atom p).jReal -
          (entry.toPoint.jReal + S / 4)| ≤ Jerr := by
    have hlt :
        |(((lemma79EndpointFreshPointAt entry atom p).j : ℕ) : ℝ) -
            horizontalCenter| < horizontalSourceThreshold := by
      exact lt_of_not_ge (fun h => hnotBounds (Or.inr h))
    rw [← hcenter]
    exact le_trans (by simpa [TaoSection7Point.jReal] using hlt.le) hJerr
  have hnew_ne_old : new ≠ old := by
    intro heq
    subst new
    have hheight := TaoSection7Triangle.mem_height_le hnew_mem
    omega
  have hrow :
      OutsideEprimeBadLowerTipRowData old new entry.toPoint
        (lemma79EndpointFreshPointAt entry atom p) S Lerr Jerr gap :=
    outsideEprimeBadLowerTipRowData_of_endpoint_estimates
      hbase hnew_mem hS hlower hupper hj hgap0 hL0 hJ0 hmargin
  have hraw :
      RawOutsideEprimeCommonPointEndpointData old new
        (lemma79EndpointFreshPointAt entry atom p) gap K B :=
    rawOutsideEprimeCommonPointEndpointData_of_rowData
      hrow hgapKB hLerrKB
  rcases rawOutsideEprimeCommonPointEndpointData_to_center_nearSigma
      hpair hold hnew_family hnew_ne_old (hsize.trans hnew_size)
      hJgeo hradius hraw with ⟨c, _, hc⟩
  exact ⟨c, hc⟩

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
