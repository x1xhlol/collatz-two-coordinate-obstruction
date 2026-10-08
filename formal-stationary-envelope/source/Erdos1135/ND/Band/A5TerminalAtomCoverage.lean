import Erdos1135.ND.Band.A5GoodEPrimeIngress
import Erdos1135.ND.Band.A5GoodTimeLocalization
import Erdos1135.ND.Band.A5TerminalAtoms
import Erdos1135.Tao.Section5.AffineAtomReverse
import Erdos1135.Tao.Section5.PassEventPartition

/-!
# A5 FullGood-Gated Terminal-Atom Coverage

This leaf combines the two deterministic FullGood ingress routes.  It proves
the exact band-pass/terminal-atom event equality while keeping FullGood on
both sides.  Probability transfer and the one-time complement charge remain
separate downstream steps.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- A FullGood first passage from an exact band produces one member of the
unrestricted original-J3 terminal-atom union. -/
theorem ndA5PassEventAtTime_mem_terminalAtomUnion_of_fullPrefixGood
    {B n j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {N : Tao.TaoOddNat} {E : Set ℕ}
    (descent : Tao.TaoSection5DescentScaleFacts B)
    (time : Tao.TaoSection5PassTimeLocalizationFacts B)
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hWn0 : 10 * ndA5TubeWidth B C ≤
      (Tao.taoSection5N0 B : ℝ))
    (hWlarge : 6 ≤ ndA5TubeWidth B C)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hj : j < ndA5BandCount B branch)
    (hband : N.1 ∈ ndA5OddBand B branch j)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hpass : Tao.taoSection5PassEventAtTime B N.1 n E) :
    N ∈ ndA5TerminalAtomUnion B branch C j E := by
  classical
  have hn0 := ndA5_firstHit_le_n0_of_fullPrefixGood
    descent hWn0 hj hband hgood hpass.1
  have hnWindow := ndA5_firstHit_mem_paddedBandWindow_of_fullPrefixGood
    descent time hWn0 hWlarge hj hband hgood hpass.1
  have ht2 : NDA5T2ScaleFacts B n C :=
    ndA5PaddedBandWindow_t2_of_guards
      descent.one_le_B hlogB hpadding hj hnWindow
  let nu := n - Tao.taoSection5M0 B
  let as := Tao.syracuseValuationPNatList nu N.1 N.2
  let L := Tao.taoTupleWeight as
  let M := (Tao.syracuse^[nu]) N.1
  have hgoodNu := ndA5FullPrefixGoodEvent_prefix hgood ht2.sub_le_n0
  have htake : as.take nu = as := by
    dsimp [as]
    exact Tao.syracuseValuationPNatList_take_of_le N.2 le_rfl
  have hdeviationRaw := hgoodNu.2 nu le_rfl
  rw [htake] at hdeviationRaw
  have hdeviation :
      |(L : ℝ) - 2 * (nu : ℝ)| < ndA5TubeWidth B C := by
    simpa only [L] using hdeviationRaw
  have hwidthNu :
      ndA5TubeWidth B C ≤ (nu : ℝ) / 8 := by
    simpa only [nu] using ht2.width_le_nu_div_eight
  have hnu0 : (0 : ℝ) ≤ (nu : ℝ) := Nat.cast_nonneg nu
  have hWleNu : ndA5TubeWidth B C ≤ (nu : ℝ) := by
    nlinarith
  have hnuLReal : (nu : ℝ) < (L : ℝ) := by
    nlinarith [(abs_lt.mp hdeviation).1]
  have hL3nuReal : (L : ℝ) < 3 * (nu : ℝ) := by
    nlinarith [(abs_lt.mp hdeviation).2]
  have hnuL : nu ≤ L := by exact_mod_cast hnuLReal.le
  have hL3nu : L ≤ 3 * nu := by exact_mod_cast hL3nuReal.le
  have hLmem : L ∈ ndA5TerminalTotals B C n := by
    apply mem_ndA5TerminalTotals_iff.mpr
    exact
      ⟨by simpa only [nu] using hnuL,
        by simpa only [nu] using hL3nu,
        by simpa only [nu, L] using hdeviation⟩
  have hMmem : M ∈ Tao.taoSection5EPrime B E := by
    exact ndA5PassEventAtTime_shifted_mem_EPrime_of_fullPrefixGood
      lost ht2.m0_le hn0 hwidth hgood hpass
  let a : NDFixedTotalValuations nu L :=
    ⟨as, ⟨Tao.syracuseValuationPNatList_length nu N.1 N.2, rfl⟩⟩
  let u : Sym (Fin nu) (L - nu) :=
    (ndFiberExtrasEquivFixedTotal nu L hnuL).symm a
  let i : NDA5TerminalAtomIndex B branch C j E :=
    ⟨⟨n, hnWindow⟩,
      ⟨⟨L, hLmem⟩, (u, ⟨M, hMmem⟩)⟩⟩
  have hfixed : ndA5TerminalAtomFixedTotal i = a := by
    change (ndFiberExtrasEquivFixedTotal nu L _) u = a
    exact (ndFiberExtrasEquivFixedTotal nu L hnuL).apply_symm_apply a
  have hvalues : ndA5TerminalAtomValuations i = as := by
    change (ndA5TerminalAtomFixedTotal i).1 = as
    rw [hfixed]
  have hAff : Tao.taoAffList as (N.1 : ℚ) = (M : ℚ) := by
    simpa only [M] using
      (Tao.syracuse_iterate_eq_taoAffList nu N.1 N.2).symm
  apply Set.mem_iUnion.mpr
  refine ⟨i, hband, ?_⟩
  rw [hvalues]
  exact hAff

/-- FullGood turns membership in one unrestricted terminal atom back into the
original passage event at that atom's padded time. -/
theorem ndA5TerminalAtom_mem_passEventAtTime_of_fullPrefixGood
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hbudget : Tao.taoSection5ReversePrefixScalarBudget B)
    {N : Tao.TaoOddNat}
    (hatom : N ∈ ndA5TerminalAtom i)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C) :
    Tao.taoSection5PassEventAtTime B N.1 i.1.1 E := by
  have hMmem := ndA5TerminalAtom_endpoint_mem i
  have hModd := (Tao.mem_taoSection5EPrime_iff.mp hMmem).2.2.1
  have hdecode :=
    (Tao.taoAffList_eq_oddNat_iff
      (ndA5TerminalAtomValuations i) N.2 hModd).mp hatom.2
  have hvalues :
      Tao.syracuseValuationPNatList
          (i.1.1 - Tao.taoSection5M0 B) N.1 N.2 =
        ndA5TerminalAtomValuations i := by
    simpa only [ndA5TerminalAtomValuations_length] using hdecode.1
  have htypActual := ndA5FullPrefixGoodEvent_sourceTypicalPrefix
    hwidth hgood ht2.sub_le_n0
  have htypAtom :
      Tao.taoSection5SourceTypicalTuple B
        (i.1.1 - Tao.taoSection5M0 B)
        (ndA5TerminalAtomValuations i) := by
    rw [← hvalues]
    exact htypActual
  have has :
      ndA5TerminalAtomValuations i ∈
        Tao.taoSection5TypicalTuples B
          (i.1.1 - Tao.taoSection5M0 B) :=
    Tao.mem_taoSection5TypicalTuples_iff.mpr
      (Tao.TaoSection5SourceTypicalTuple.to_closed htypAtom)
  exact Tao.taoSection5PassEventAtTime_of_affineAtom
    ht2.m0_le ht2.sub_le_n0 has hMmem hatom.2 hbudget

/-- On strict FullGood, the actual band passage event is exactly the finite
unrestricted original-J3 terminal-atom union. -/
theorem ndA5PassBand_inter_fullPrefixGood_eq_terminalAtomUnion_inter
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {E : Set ℕ}
    (descent : Tao.TaoSection5DescentScaleFacts B)
    (time : Tao.TaoSection5PassTimeLocalizationFacts B)
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hbudget : Tao.taoSection5ReversePrefixScalarBudget B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hWn0 : 10 * ndA5TubeWidth B C ≤
      (Tao.taoSection5N0 B : ℝ))
    (hWlarge : 6 ≤ ndA5TubeWidth B C)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hj : j < ndA5BandCount B branch) :
    ((Tao.taoSection5PassEvent B E ∩
          {N | N.1 ∈ ndA5OddBand B branch j}) ∩
        ndA5FullPrefixGoodEvent B C) =
      ndA5TerminalAtomUnion B branch C j E ∩
        ndA5FullPrefixGoodEvent B C := by
  ext N
  constructor
  · rintro ⟨⟨⟨n, hpass⟩, hband⟩, hgood⟩
    exact
      ⟨ndA5PassEventAtTime_mem_terminalAtomUnion_of_fullPrefixGood
          descent time lost hlogB hpadding hWn0 hWlarge hwidth hj
          hband hgood hpass,
        hgood⟩
  · rintro ⟨hunion, hgood⟩
    rcases Set.mem_iUnion.mp hunion with ⟨i, hatom⟩
    have ht2 : NDA5T2ScaleFacts B i.1.1 C :=
      ndA5PaddedBandWindow_t2_of_guards
        descent.one_le_B hlogB hpadding hj i.1.2
    have hpass := ndA5TerminalAtom_mem_passEventAtTime_of_fullPrefixGood
      i ht2 hwidth hbudget hatom hgood
    exact ⟨⟨⟨i.1.1, hpass⟩, hatom.1⟩, hgood⟩

end

end ND
end Erdos1135
