import Erdos1135.ND.Band.A5BandNormalizer
import Erdos1135.ND.Band.A5PaddedBandDiameter
import Erdos1135.ND.Fourier.FiberConditioning
import Erdos1135.Tao.Syracuse.AffineOdd
import Erdos1135.Tao.Syracuse.OddSource

/-!
# A5 Finite Unrestricted Terminal Atoms

This leaf defines the finite original-`J_j` terminal carrier and proves its
actual-band affine atoms pairwise disjoint.  The index retains every endpoint
in `EPrime`; it contains no trimmed schedule, prefix-typicality, residue, or
interior-shift filter.
-/

namespace Erdos1135
namespace ND

open Filter

noncomputable section

/-- Terminal totals in the guarded fixed-total regime. -/
noncomputable def ndA5TerminalTotals
    (B : ℕ) (C : ℝ) (n : ℕ) : Finset ℕ :=
  let nu := n - Tao.taoSection5M0 B
  (Finset.Icc nu (3 * nu)).filter fun L =>
    |(L : ℝ) - 2 * (nu : ℝ)| < ndA5TubeWidth B C

theorem mem_ndA5TerminalTotals_iff
    {B n L : ℕ} {C : ℝ} :
    L ∈ ndA5TerminalTotals B C n ↔
      n - Tao.taoSection5M0 B ≤ L ∧
        L ≤ 3 * (n - Tao.taoSection5M0 B) ∧
          |(L : ℝ) - 2 * ((n - Tao.taoSection5M0 B : ℕ) : ℝ)| <
            ndA5TubeWidth B C := by
  simp [ndA5TerminalTotals, and_assoc]

/-- Finite unrestricted terminal data: padded time, terminal total, one
fixed-total valuation tuple, and one endpoint in the full `EPrime` target. -/
abbrev NDA5TerminalAtomIndex
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :=
  Σ n : {n // n ∈ ndA5PaddedBandWindow B branch C j},
    Σ L : {L // L ∈ ndA5TerminalTotals B C n.1},
      Sym (Fin (n.1 - Tao.taoSection5M0 B))
          (L.1 - (n.1 - Tao.taoSection5M0 B)) ×
        {M : ℕ // M ∈ Tao.taoSection5EPrime B E}

noncomputable instance ndA5TerminalAtomIndexFintype
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :
    Fintype (NDA5TerminalAtomIndex B branch C j E) := by
  classical
  unfold NDA5TerminalAtomIndex
  infer_instance

@[simp] theorem ndA5TerminalAtom_time_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    i.1.1 ∈ ndA5PaddedBandWindow B branch C j :=
  i.1.2

@[simp] theorem ndA5TerminalAtom_total_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    i.2.1.1 ∈ ndA5TerminalTotals B C i.1.1 :=
  i.2.1.2

theorem ndA5TerminalAtom_nu_le_total
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    i.1.1 - Tao.taoSection5M0 B ≤ i.2.1.1 :=
  (mem_ndA5TerminalTotals_iff.mp i.2.1.2).1

@[simp] theorem ndA5TerminalAtom_endpoint_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    i.2.2.2.1 ∈ Tao.taoSection5EPrime B E :=
  i.2.2.2.2

/-- Decode the finite `Sym` field to the exact fixed-total positive list. -/
noncomputable def ndA5TerminalAtomFixedTotal
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    NDFixedTotalValuations
      (i.1.1 - Tao.taoSection5M0 B) i.2.1.1 :=
  ndFiberExtrasEquivFixedTotal
    (i.1.1 - Tao.taoSection5M0 B) i.2.1.1
    (ndA5TerminalAtom_nu_le_total i) i.2.2.1

noncomputable def ndA5TerminalAtomValuations
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : List ℕ+ :=
  (ndA5TerminalAtomFixedTotal i).1

@[simp] theorem ndA5TerminalAtomValuations_length
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    (ndA5TerminalAtomValuations i).length =
      i.1.1 - Tao.taoSection5M0 B := by
  simpa only [ndA5TerminalAtomValuations] using
    (ndA5TerminalAtomFixedTotal i).2.1

@[simp] theorem ndA5TerminalAtomValuations_weight
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    Tao.taoTupleWeight (ndA5TerminalAtomValuations i) = i.2.1.1 := by
  simpa only [ndA5TerminalAtomValuations] using
    (ndA5TerminalAtomFixedTotal i).2.2

/-- The actual terminal atom retains the physical half-open band selector.
Incompatible affine fibers are simply empty. -/
def ndA5TerminalAtom
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : Set Tao.TaoOddNat :=
  {N | N.1 ∈ ndA5OddBand B branch j ∧
    Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
      (i.2.2.2.1 : ℚ)}

/-- Union of all finite unrestricted terminal atoms for one physical band. -/
def ndA5TerminalAtomUnion
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) : Set Tao.TaoOddNat :=
  ⋃ i : NDA5TerminalAtomIndex B branch C j E, ndA5TerminalAtom i

private theorem ndA5TerminalAtom_time_eq_of_common_affineSource_ordered
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B)
    {i i' : NDA5TerminalAtomIndex B branch C j E} {N : Tao.TaoOddNat}
    (hAff :
      Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
        (i.2.2.2.1 : ℚ))
    (hAff' :
      Tao.taoAffList (ndA5TerminalAtomValuations i') (N.1 : ℚ) =
        (i'.2.2.2.1 : ℚ))
    (hii' : i.1.1 ≤ i'.1.1) :
    i.1.1 = i'.1.1 := by
  have hModd :=
    (Tao.mem_taoSection5EPrime_iff.mp i.2.2.2.2).2.2.1
  have hM'odd :=
    (Tao.mem_taoSection5EPrime_iff.mp i'.2.2.2.2).2.2.1
  have hdecode :=
    (Tao.taoAffList_eq_oddNat_iff
      (ndA5TerminalAtomValuations i) N.2 hModd).mp hAff
  have hdecode' :=
    (Tao.taoAffList_eq_oddNat_iff
      (ndA5TerminalAtomValuations i') N.2 hM'odd).mp hAff'
  have hend :
      (Tao.syracuse^[i.1.1 - Tao.taoSection5M0 B]) N.1 =
        i.2.2.2.1 := by
    simpa only [ndA5TerminalAtomValuations_length] using hdecode.2
  have hend' :
      (Tao.syracuse^[i'.1.1 - Tao.taoSection5M0 B]) N.1 =
        i'.2.2.2.1 := by
    simpa only [ndA5TerminalAtomValuations_length] using hdecode'.2
  have htimeI := htime i.1.1 i.1.2
  have hshift :
      i'.1.1 - Tao.taoSection5M0 B =
        (i'.1.1 - i.1.1) + (i.1.1 - Tao.taoSection5M0 B) := by
    omega
  have hMM' :
      (Tao.syracuse^[i'.1.1 - i.1.1]) i.2.2.2.1 = i'.2.2.2.1 := by
    rw [← hend, ← Function.iterate_add_apply, ← hshift]
    exact hend'
  have hfirst :=
    (Tao.mem_taoSection5EPrime_iff.mp i.2.2.2.2).2.2.2.1
  have hfirst' :=
    (Tao.mem_taoSection5EPrime_iff.mp i'.2.2.2.2).2.2.2.1
  have hgap := hdiam i.1.1 i.1.2 i'.1.1 i'.1.2 hii'
  have htail := Tao.syracuseFirstHitAtMost_tail hfirst
    hgap
  rw [hMM'] at htail
  have hsub :
      Tao.taoSection5M0 B - (i'.1.1 - i.1.1) =
        Tao.taoSection5M0 B :=
    Tao.syracuseFirstHitAtMost_unique htail hfirst'
  omega

/-- Two fixed-band terminal indices admitting the same odd affine source are
equal.  Physical-band membership is deliberately absent: this is the exact
injectivity socket needed when a nominal-only source lies in a boundary shell. -/
theorem ndA5TerminalAtomIndex_eq_of_common_affineSource
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B)
    {i i' : NDA5TerminalAtomIndex B branch C j E} {N : Tao.TaoOddNat}
    (hAffI :
      Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
        (i.2.2.2.1 : ℚ))
    (hAffI' :
      Tao.taoAffList (ndA5TerminalAtomValuations i') (N.1 : ℚ) =
        (i'.2.2.2.1 : ℚ)) :
    i = i' := by
  have htimeEq : i.1.1 = i'.1.1 := by
    rcases le_total i.1.1 i'.1.1 with hii' | hi'i
    · exact ndA5TerminalAtom_time_eq_of_common_affineSource_ordered
        htime hdiam hAffI hAffI' hii'
    · exact (ndA5TerminalAtom_time_eq_of_common_affineSource_ordered
        htime hdiam hAffI' hAffI hi'i).symm
  rcases i with ⟨⟨n, hn⟩, ⟨⟨L, hL⟩, u, ⟨M, hM⟩⟩⟩
  rcases i' with ⟨⟨n', hn'⟩, ⟨⟨L', hL'⟩, u', ⟨M', hM'⟩⟩⟩
  change n = n' at htimeEq
  subst n'
  let hnuL : n - Tao.taoSection5M0 B ≤ L :=
    (mem_ndA5TerminalTotals_iff.mp hL).1
  let hnuL' : n - Tao.taoSection5M0 B ≤ L' :=
    (mem_ndA5TerminalTotals_iff.mp hL').1
  let a : NDFixedTotalValuations (n - Tao.taoSection5M0 B) L :=
    ndFiberExtrasEquivFixedTotal
      (n - Tao.taoSection5M0 B) L hnuL u
  let a' : NDFixedTotalValuations (n - Tao.taoSection5M0 B) L' :=
    ndFiberExtrasEquivFixedTotal
      (n - Tao.taoSection5M0 B) L' hnuL' u'
  have hAff : Tao.taoAffList a.1 (N.1 : ℚ) = (M : ℚ) := by
    simpa [ndA5TerminalAtomValuations,
      ndA5TerminalAtomFixedTotal, a, hnuL] using hAffI
  have hAff' : Tao.taoAffList a'.1 (N.1 : ℚ) = (M' : ℚ) := by
    simpa [ndA5TerminalAtomValuations,
      ndA5TerminalAtomFixedTotal, a', hnuL'] using hAffI'
  have hModd := (Tao.mem_taoSection5EPrime_iff.mp hM).2.2.1
  have hM'odd := (Tao.mem_taoSection5EPrime_iff.mp hM').2.2.1
  have hdecode := (Tao.taoAffList_eq_oddNat_iff a.1 N.2 hModd).mp hAff
  have hdecode' :=
    (Tao.taoAffList_eq_oddNat_iff a'.1 N.2 hM'odd).mp hAff'
  have haa' : a.1 = a'.1 := by
    calc
      a.1 = Tao.syracuseValuationPNatList a.1.length N.1 N.2 :=
        hdecode.1.symm
      _ = Tao.syracuseValuationPNatList a'.1.length N.1 N.2 := by
        rw [a.2.1, a'.2.1]
      _ = a'.1 := hdecode'.1
  have hLL' : L = L' := by
    calc
      L = Tao.taoTupleWeight a.1 := a.2.2.symm
      _ = Tao.taoTupleWeight a'.1 := congrArg Tao.taoTupleWeight haa'
      _ = L' := a'.2.2
  have hMM'rat : (M : ℚ) = (M' : ℚ) := by
    calc
      (M : ℚ) = Tao.taoAffList a.1 (N.1 : ℚ) := hAff.symm
      _ = Tao.taoAffList a'.1 (N.1 : ℚ) := by rw [haa']
      _ = (M' : ℚ) := hAff'
  have hMM' : M = M' := by exact_mod_cast hMM'rat
  subst L'
  subst M'
  have huu' : u = u' := by
    apply (ndFiberExtrasEquivFixedTotal
      (n - Tao.taoSection5M0 B) L hnuL).injective
    apply Subtype.ext
    simpa [a, a'] using haa'
  subst u'
  rfl

/-- Two terminal indices with a common actual-band affine source are equal.
This preserves the original-J3 no-double-count API as a corollary of the
physical-membership-free affine-source theorem. -/
theorem ndA5TerminalAtomIndex_eq_of_common_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B)
    {i i' : NDA5TerminalAtomIndex B branch C j E} {N : Tao.TaoOddNat}
    (hi : N ∈ ndA5TerminalAtom i)
    (hi' : N ∈ ndA5TerminalAtom i') :
    i = i' :=
  ndA5TerminalAtomIndex_eq_of_common_affineSource
    htime hdiam hi.2 hi'.2

theorem ndA5TerminalAtoms_pairwiseDisjoint
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B) :
    Set.PairwiseDisjoint
      (Set.univ : Set (NDA5TerminalAtomIndex B branch C j E))
      ndA5TerminalAtom := by
  intro i _hi i' _hi' hii'
  change Disjoint (ndA5TerminalAtom i) (ndA5TerminalAtom i')
  rw [Set.disjoint_left]
  intro N hN hN'
  exact hii' (ndA5TerminalAtomIndex_eq_of_common_mem
    htime hdiam hN hN')

/-- Source-facing eventual disjointness on every valid original-J3 band. -/
theorem eventually_ndA5TerminalAtoms_pairwiseDisjoint
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ) (E : Set ℕ),
        j < ndA5BandCount B branch →
          Set.PairwiseDisjoint
            (Set.univ : Set (NDA5TerminalAtomIndex B branch C j E))
            ndA5TerminalAtom := by
  filter_upwards
    [eventually_ndA5M0_lt_of_mem_paddedBandWindow C hC,
      eventually_ndA5PaddedBandWindow_diameter_le_m0 C hC]
      with B htime hdiam
  intro branch j E hj
  exact ndA5TerminalAtoms_pairwiseDisjoint
    (htime branch j hj) (hdiam branch j hj)

end

end ND
end Erdos1135
