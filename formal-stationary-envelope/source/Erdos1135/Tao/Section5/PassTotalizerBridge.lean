import Erdos1135.Tao.Section3
import Erdos1135.Tao.Probability.LogWindowResidue
import Erdos1135.Tao.Section5.PassEventPartition

/-!
# Section 5 Passage Totalizer Bridge

This leaf compares the genuine Section 5 first-passage event with Tao's total
passage location, which assigns the artificial endpoint `1` on no-hit inputs.
The comparison is signed: totalization can only add mass, and the added mass is
bounded by the no-hit probability.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- A genuine passage into a bounded endpoint event is exactly a hit whose
totalized passage location belongs to that event. -/
theorem mem_taoSection5PassEvent_subtypeVal_image_iff
    {B : ℕ} (hB : 1 ≤ B) (N : TaoOddNat)
    (A : Set {M : ℕ // M ≤ B}) :
    N ∈ taoSection5PassEvent B (Subtype.val '' A) ↔
      syracuseHitsAtMost N.1 B ∧
        syracusePassLocationOrOne B N.1 hB ∈ A := by
  change (∃ n, syracuseFirstHitAtMost B N.1 n ∧
      (syracuse^[n]) N.1 ∈ Subtype.val '' A) ↔ _
  constructor
  · rintro ⟨n, hfirst, M, hMA, hM⟩
    let hhit : syracuseHitsAtMost N.1 B := ⟨n, hfirst.1⟩
    have hn : n = syracuseFirstPassageTime N.1 B hhit :=
      syracuseFirstHitAtMost_unique hfirst
        (syracuseFirstHitAtMost_of_hitsAtMost N.1 B hhit)
    have hloc : syracusePassLocationOrOne B N.1 hB = M := by
      unfold syracusePassLocationOrOne
      rw [syracusePassLocationAtMostOrOne_of_hitsAtMost hB hhit]
      apply Subtype.ext
      change (syracuse^[syracuseFirstPassageTime N.1 B hhit]) N.1 = M.1
      rw [← hn]
      exact hM.symm
    refine ⟨hhit, ?_⟩
    rw [hloc]
    exact hMA
  · rintro ⟨hhit, hA⟩
    refine ⟨syracuseFirstPassageTime N.1 B hhit,
      syracuseFirstHitAtMost_of_hitsAtMost N.1 B hhit, ?_⟩
    refine ⟨syracusePassLocationOrOne B N.1 hB, hA, ?_⟩
    unfold syracusePassLocationOrOne
    rw [syracusePassLocationAtMostOrOne_of_hitsAtMost hB hhit]

/-- If the artificial endpoint `1` is excluded, totalized membership is
exactly genuine first-passage membership. -/
theorem mem_taoSection5PassEvent_subtypeVal_image_iff_totalized_of_one_not_mem
    {B : ℕ} (hB : 1 ≤ B) (N : TaoOddNat)
    (A : Set {M : ℕ // M ≤ B})
    (hone : (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∉ A) :
    N ∈ taoSection5PassEvent B (Subtype.val '' A) ↔
      syracusePassLocationOrOne B N.1 hB ∈ A := by
  constructor
  · intro hpass
    exact
      (mem_taoSection5PassEvent_subtypeVal_image_iff hB N A).mp hpass |>.2
  · intro htotal
    apply (mem_taoSection5PassEvent_subtypeVal_image_iff hB N A).mpr
    have hhit : syracuseHitsAtMost N.1 B := by
      by_contra hnot
      unfold syracusePassLocationOrOne at htotal
      rw [syracusePassLocationAtMostOrOne_of_not_hitsAtMost hB hnot] at htotal
      exact hone htotal
    exact ⟨hhit, htotal⟩

/-- An endpoint event excluding `1` has exactly the same mass under the
totalized passage law and the genuine Section 5 passage event. -/
theorem taoSection5_totalPassMass_eq_genuinePassageMass_of_one_not_mem
    {B lo hi : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (A : Set {M : ℕ // M ≤ B})
    (hone : (⟨1, hB⟩ : {M : ℕ // M ≤ B}) ∉ A) :
    pmfProb (syracusePassLocationLaw lo hi B hB hmass) A =
      ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
        (taoSection5PassEvent B (Subtype.val '' A))).toReal := by
  rw [pmfProb_syracusePassLocationLaw_preimage]
  rw [oddLogWindowOddNatPMF, PMF.toOuterMeasure_map_apply,
    ← pmfProb_eq_toOuterMeasure_toReal]
  apply congrArg (pmfProb (oddLogWindowPMF lo hi hmass))
  ext N
  change syracusePassLocationOrOne B N.1 hB ∈ A ↔
    oddLogWindowValueToOddNat N ∈
      taoSection5PassEvent B (Subtype.val '' A)
  exact
    (mem_taoSection5PassEvent_subtypeVal_image_iff_totalized_of_one_not_mem
      hB (oddLogWindowValueToOddNat N) A hone).symm

/-- Totalizing genuine first passage adds nonnegative mass and adds at most the
no-hit mass. All three quantities are pulled back to the same finite source
window; in particular, no complement identity for `Subtype.val '' A` is used.
-/
theorem taoSection5_totalPassMass_sub_genuinePassageMass_nonneg_le
    {B lo hi : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (A : Set {M : ℕ // M ≤ B}) :
    let totalMass :=
      pmfProb (syracusePassLocationLaw lo hi B hB hmass) A
    let genuineMass :=
      ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
        (taoSection5PassEvent B (Subtype.val '' A))).toReal
    let noHitMass := syracuseNoHitWindowProb B lo hi hmass
    0 ≤ totalMass - genuineMass ∧
      totalMass - genuineMass ≤ noHitMass := by
  let p := oddLogWindowPMF lo hi hmass
  let totalEvent : Set {N : ℕ // N ∈ oddLogWindow lo hi} :=
    {N | syracusePassLocationOrOne B N.1 hB ∈ A}
  let genuineEvent : Set {N : ℕ // N ∈ oddLogWindow lo hi} :=
    {N | oddLogWindowValueToOddNat N ∈
      taoSection5PassEvent B (Subtype.val '' A)}
  let noHitEvent : Set {N : ℕ // N ∈ oddLogWindow lo hi} :=
    {N | N.1 ∈ syracuseNoHitAtMost B}
  have hgenuine_subset : genuineEvent ⊆ totalEvent := by
    intro N hN
    change oddLogWindowValueToOddNat N ∈
      taoSection5PassEvent B (Subtype.val '' A) at hN
    change syracusePassLocationOrOne B N.1 hB ∈ A
    exact
      (mem_taoSection5PassEvent_subtypeVal_image_iff hB
        (oddLogWindowValueToOddNat N) A).mp hN |>.2
  have htotal_diff_subset : totalEvent \ genuineEvent ⊆ noHitEvent := by
    intro N hN
    rcases hN with ⟨htotal_mem, hnot_genuine⟩
    change syracusePassLocationOrOne B N.1 hB ∈ A at htotal_mem
    change ¬ oddLogWindowValueToOddNat N ∈
      taoSection5PassEvent B (Subtype.val '' A) at hnot_genuine
    change N.1 ∈ syracuseNoHitAtMost B
    intro hhit
    exact hnot_genuine
      ((mem_taoSection5PassEvent_subtypeVal_image_iff hB
        (oddLogWindowValueToOddNat N) A).mpr ⟨hhit, htotal_mem⟩)
  have htotal :
      pmfProb (syracusePassLocationLaw lo hi B hB hmass) A =
        pmfProb p totalEvent := by
    rw [pmfProb_syracusePassLocationLaw_preimage]
  have hgenuine :
      ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
          (taoSection5PassEvent B (Subtype.val '' A))).toReal =
        pmfProb p genuineEvent := by
    rw [oddLogWindowOddNatPMF, PMF.toOuterMeasure_map_apply,
      ← pmfProb_eq_toOuterMeasure_toReal]
    rfl
  have hnoHit :
      syracuseNoHitWindowProb B lo hi hmass = pmfProb p noHitEvent := by
    rfl
  dsimp only
  rw [htotal, hgenuine, hnoHit]
  constructor
  · exact sub_nonneg.mpr (pmfProb_mono p hgenuine_subset)
  · exact pmfProb_diff_le_of_diff_subset p htotal_diff_subset

end

end Tao
end Erdos1135
