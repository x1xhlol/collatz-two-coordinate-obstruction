import Erdos1135.ND.Band.A5ExactAffineCorrection
import Erdos1135.ND.Band.A5TerminalAtomMass
import Erdos1135.Tao.Probability.LogWindowFloorPerturbation
import Erdos1135.Tao.Syracuse.AffineReciprocal
import Erdos1135.Tao.Syracuse.AffineResidue

/-!
# A5 Actual-Support Affine Denominator Comparison

This leaf replaces the exact affine denominator `M - F` by `M` while
retaining the physical-band support selector.  The aggregate error is charged
to the disjoint terminal-atom union mass, with no atom-count loss.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- The unique natural candidate selected by one terminal affine equation. -/
noncomputable def ndA5TerminalAtomCandidate
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : ℕ :=
  Tao.taoAffineSourceCandidate
    (i.1.1 - Tao.taoSection5M0 B)
    (ndA5TerminalAtomValuations i) i.2.2.2.1

/-- Proof-free residue compatibility of one terminal affine equation. -/
noncomputable def ndA5TerminalAtomCompatible
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : Prop :=
  (i.2.2.2.1 : ZMod
      (3 ^ (i.1.1 - Tao.taoSection5M0 B))) =
    Tao.taoAffineOffsetZMod
      (i.1.1 - Tao.taoSection5M0 B)
      (ndA5TerminalAtomValuations i)

noncomputable instance ndA5TerminalAtomCompatibleDecidable
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    Decidable (ndA5TerminalAtomCompatible i) :=
  Classical.propDecidable _

/-- Exact proof-free support selector for one physical-band terminal atom.
It records both affine residue compatibility and membership of the unique
candidate in the same physical half-open band. -/
noncomputable def ndA5TerminalAtomSupported
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : Prop :=
  ndA5TerminalAtomCompatible i ∧
    ndA5TerminalAtomCandidate i ∈ ndA5OddBand B branch j

noncomputable instance ndA5TerminalAtomSupportedDecidable
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    Decidable (ndA5TerminalAtomSupported i) :=
  Classical.propDecidable _

/-- Any exhibited source is the unique natural source in its exact affine
terminal atom. -/
theorem ndA5TerminalAtomSourceFinset_eq_singleton_of_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j N : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (hN : N ∈ ndA5TerminalAtomSourceFinset i) :
    ndA5TerminalAtomSourceFinset i = {N} := by
  classical
  ext N'
  rw [mem_ndA5TerminalAtomSourceFinset_iff]
  simp only [Finset.mem_singleton]
  constructor
  · intro hN'
    have hCandidateN' :=
      Tao.taoAffineSourceCandidate_eq_of_taoAffList_eq
        (ndA5TerminalAtomValuations_length i) hN'.2
    have hNdata := (mem_ndA5TerminalAtomSourceFinset_iff i).mp hN
    have hCandidateN :=
      Tao.taoAffineSourceCandidate_eq_of_taoAffList_eq
        (ndA5TerminalAtomValuations_length i) hNdata.2
    exact hCandidateN'.symm.trans hCandidateN
  · rintro rfl
    exact (mem_ndA5TerminalAtomSourceFinset_iff i).mp hN

/-- Endpoint room turns compatibility into the positive odd candidate and its
exact affine equation.  This packet is independent of physical-band support. -/
theorem ndA5TerminalAtomCandidate_odd_and_affine
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C)
    (hcompat : ndA5TerminalAtomCompatible i) :
    Odd (ndA5TerminalAtomCandidate i) ∧
      Tao.taoAffList (ndA5TerminalAtomValuations i)
          (ndA5TerminalAtomCandidate i : ℚ) =
        (i.2.2.2.1 : ℚ) := by
  have hMdata := Tao.mem_taoSection5EPrime_iff.mp
    (ndA5TerminalAtom_endpoint_mem i)
  have hMcanonical :
      i.2.2.2.1 ∈ Tao.taoSection5CanonicalLostWindow B :=
    Finset.mem_Icc.mpr ⟨hMdata.1, hMdata.2.1⟩
  have hroom :
      2 * 3 ^ (i.1.1 - Tao.taoSection5M0 B) < i.2.2.2.1 :=
    facts.endpoint_room ht2.sub_le_n0 hMcanonical
  obtain ⟨N, hAff, _hunique⟩ :=
    Tao.existsUnique_taoAffList_eq_of_affineOffsetZMod
      (ndA5TerminalAtomValuations_length i) hMdata.2.2.1 hroom hcompat
  have hCandidate : ndA5TerminalAtomCandidate i = N.1 := by
    unfold ndA5TerminalAtomCandidate
    exact Tao.taoAffineSourceCandidate_eq_of_taoAffList_eq
      (ndA5TerminalAtomValuations_length i) hAff
  rw [hCandidate]
  exact ⟨N.2, hAff⟩

/-- Inside one fixed band, compatible terminal equations have distinct affine
source candidates.  The fixed-band scope prevents any cross-band multiplicity
claim. -/
theorem ndA5TerminalAtomCandidate_injOn_compatible
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B)
    (ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C) :
    Set.InjOn
      (fun i : NDA5TerminalAtomIndex B branch C j E =>
        ndA5TerminalAtomCandidate i)
      {i | ndA5TerminalAtomCompatible i} := by
  intro i hi i' hi' hcand
  have pi := ndA5TerminalAtomCandidate_odd_and_affine
    facts i (ht2 i) hi
  have pi' := ndA5TerminalAtomCandidate_odd_and_affine
    facts i' (ht2 i') hi'
  let N : Tao.TaoOddNat := ⟨ndA5TerminalAtomCandidate i, pi.1⟩
  apply ndA5TerminalAtomIndex_eq_of_common_affineSource
    htime hdiam (N := N)
  · simpa only [N] using pi.2
  · have hAff' := pi'.2
    change ndA5TerminalAtomCandidate i =
      ndA5TerminalAtomCandidate i' at hcand
    rw [← hcand] at hAff'
    simpa only [N] using hAff'

/-- Under the neutral endpoint-room packet, the actual source finset is
exactly the supported affine candidate, or empty. -/
theorem ndA5TerminalAtomSourceFinset_eq_ite_supported
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    ndA5TerminalAtomSourceFinset i =
      if ndA5TerminalAtomSupported i then
        {ndA5TerminalAtomCandidate i}
      else ∅ := by
  classical
  by_cases hsupp : ndA5TerminalAtomSupported i
  · rw [if_pos hsupp]
    have hsuppData :
        ndA5TerminalAtomCompatible i ∧
          ndA5TerminalAtomCandidate i ∈ ndA5OddBand B branch j := by
      simpa only [ndA5TerminalAtomSupported] using hsupp
    have hpacket := ndA5TerminalAtomCandidate_odd_and_affine
      facts i ht2 hsuppData.1
    have hNsource :
        ndA5TerminalAtomCandidate i ∈ ndA5TerminalAtomSourceFinset i :=
      (mem_ndA5TerminalAtomSourceFinset_iff i).2
        ⟨hsuppData.2, hpacket.2⟩
    exact ndA5TerminalAtomSourceFinset_eq_singleton_of_mem i hNsource
  · rw [if_neg hsupp]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨N, hN⟩
    apply hsupp
    have hNdata := (mem_ndA5TerminalAtomSourceFinset_iff i).mp hN
    let Nodd : Tao.TaoOddNat :=
      ⟨N, Nat.odd_iff.mpr (mem_ndA5OddBand.mp hNdata.1).2.2⟩
    have hAffOdd :
        Tao.taoAffList (ndA5TerminalAtomValuations i)
            (Nodd.1 : ℚ) = (i.2.2.2.1 : ℚ) := by
      simpa only [Nodd] using hNdata.2
    have hcompat := Tao.taoAffineOffsetZMod_eq_of_taoAffList_eq
      (ndA5TerminalAtomValuations_length i) hAffOdd
    have hCandidate :=
      Tao.taoAffineSourceCandidate_eq_of_taoAffList_eq
        (ndA5TerminalAtomValuations_length i) hNdata.2
    have hCandidate' : ndA5TerminalAtomCandidate i = N := by
      simpa only [ndA5TerminalAtomCandidate] using hCandidate
    simpa only [ndA5TerminalAtomSupported, hCandidate'] using
      And.intro hcompat hNdata.1

/-- Actual support is equivalent to the explicit residue-and-band selector. -/
theorem ndA5TerminalAtomSourceFinset_nonempty_iff_supported
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    (ndA5TerminalAtomSourceFinset i).Nonempty ↔
      ndA5TerminalAtomSupported i := by
  rw [ndA5TerminalAtomSourceFinset_eq_ite_supported facts i ht2]
  by_cases hsupp : ndA5TerminalAtomSupported i <;> simp [hsupp]

/-- A nonempty actual source finset has the exact reciprocal logarithmic
mass, together with positivity of the affine denominator. -/
theorem ndA5TerminalAtomSourceFinset_denominator_pos_and_logMass_eq_reciprocal
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (hne : (ndA5TerminalAtomSourceFinset i).Nonempty) :
    0 < (i.2.2.2.1 : ℝ) -
          (Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ) ∧
      Tao.logFinsetMass (ndA5TerminalAtomSourceFinset i) =
        (((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
            Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
          ((i.2.2.2.1 : ℝ) -
            (Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ))) := by
  classical
  obtain ⟨N, hN⟩ := hne
  have hNdata := (mem_ndA5TerminalAtomSourceFinset_iff i).mp hN
  let Nodd : Tao.TaoOddNat :=
    ⟨N, Nat.odd_iff.mpr (mem_ndA5OddBand.mp hNdata.1).2.2⟩
  have hAff :
      Tao.taoAffList (ndA5TerminalAtomValuations i)
          (Nodd.1 : ℚ) = (i.2.2.2.1 : ℚ) := by
    simpa only [Nodd] using hNdata.2
  have hpacket := Tao.taoAffList_denominator_pos_and_reciprocal
    (ndA5TerminalAtomValuations_length i) hAff
  refine ⟨hpacket.1, ?_⟩
  rw [ndA5TerminalAtomSourceFinset_eq_singleton_of_mem i hN]
  simp only [Tao.logFinsetMass, Finset.sum_singleton]
  rw [Tao.logNatWeight_eq_one_div_of_pos (Odd.pos Nodd.2)]
  simpa only [Nodd] using hpacket.2

/-- Same-support ideal mass before classifying the actual source finset.  The
constant simplified reciprocal contribution is summed once for every actual
source. -/
noncomputable def ndA5HarmonicTerminalAtomSourceSumIdealMass
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : ℝ :=
  ∑ _N ∈ ndA5TerminalAtomSourceFinset i,
    ((((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
          Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
        (i.2.2.2.1 : ℝ)) /
      Tao.logFinsetMass (ndA5OddBand B branch j))

/-- Exact relative denominator identity on the actual source finset.  This
neutral core precedes residue classification and needs no scale or endpoint-
room packet. -/
theorem ndA5HarmonicTerminalAtomMass_sub_sourceSumIdeal_eq
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E) :
    let μ := ndA5HarmonicBandPMF B branch j hB hcount
    (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal -
        ndA5HarmonicTerminalAtomSourceSumIdealMass i =
      ((Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ) /
        (i.2.2.2.1 : ℝ)) *
        (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal := by
  dsimp only
  rw [ndA5HarmonicBandPMF_terminalAtomMass_eq_logFinsetMass_div]
  by_cases hne : (ndA5TerminalAtomSourceFinset i).Nonempty
  · obtain ⟨N, hN⟩ := hne
    have hsource :=
      ndA5TerminalAtomSourceFinset_eq_singleton_of_mem i hN
    have hpacket :=
      ndA5TerminalAtomSourceFinset_denominator_pos_and_logMass_eq_reciprocal
        i ⟨N, hN⟩
    have hMposNat : 0 < i.2.2.2.1 :=
      Odd.pos (Tao.mem_taoSection5EPrime_iff.mp
        (ndA5TerminalAtom_endpoint_mem i)).2.2.1
    have hMpos : (0 : ℝ) < i.2.2.2.1 := by exact_mod_cast hMposNat
    have hmassPos :
        0 < Tao.logFinsetMass (ndA5OddBand B branch j) :=
      logFinsetMass_ndA5OddBand_pos hB j hcount
    rw [hpacket.2]
    unfold ndA5HarmonicTerminalAtomSourceSumIdealMass
    rw [hsource]
    simp only [Finset.sum_singleton]
    field_simp [hpacket.1.ne', hMpos.ne', hmassPos.ne']
    ring
  · have hempty : ndA5TerminalAtomSourceFinset i = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [ndA5HarmonicTerminalAtomSourceSumIdealMass, hempty,
      Tao.logFinsetMass]

/-- Exact finite aggregate of the relative denominator defects before any
uniform ratio estimate. -/
theorem ndA5HarmonicTerminalAtomUnionMass_sub_sourceSumIdealSum_eq
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hpair :
      Set.PairwiseDisjoint
        (Set.univ : Set (NDA5TerminalAtomIndex B branch C j E))
        ndA5TerminalAtom) :
    let μ := ndA5HarmonicBandPMF B branch j hB hcount
    let U := (μ.toOuterMeasure
      (ndA5TerminalAtomUnion B branch C j E)).toReal
    U - ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomSourceSumIdealMass i =
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ((Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ) /
          (i.2.2.2.1 : ℝ)) *
          (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal := by
  classical
  dsimp only
  let μ := ndA5HarmonicBandPMF B branch j hB hcount
  rw [ndA5TerminalAtomUnion_outerMass_eq_sum μ hpair,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact ndA5HarmonicTerminalAtomMass_sub_sourceSumIdeal_eq hB hcount i

/-- Totalized exact reciprocal mass of one supported physical-band terminal
atom under the harmonic band law. -/
theorem ndA5HarmonicBandPMF_terminalAtomMass_eq_exact
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    ((ndA5HarmonicBandPMF B branch j facts.schedule.one_le_B hcount).toOuterMeasure
        (ndA5TerminalAtom i)).toReal =
      if ndA5TerminalAtomSupported i then
        ((((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
              Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
            ((i.2.2.2.1 : ℝ) -
              (Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ))) /
          Tao.logFinsetMass (ndA5OddBand B branch j))
      else 0 := by
  rw [ndA5HarmonicBandPMF_terminalAtomMass_eq_logFinsetMass_div]
  by_cases hsupp : ndA5TerminalAtomSupported i
  · rw [if_pos hsupp]
    have hne :=
      (ndA5TerminalAtomSourceFinset_nonempty_iff_supported facts i ht2).2 hsupp
    rw [(ndA5TerminalAtomSourceFinset_denominator_pos_and_logMass_eq_reciprocal
      i hne).2]
  · rw [if_neg hsupp]
    have hnotne : ¬(ndA5TerminalAtomSourceFinset i).Nonempty :=
      (not_congr
        (ndA5TerminalAtomSourceFinset_nonempty_iff_supported facts i ht2)).2
          hsupp
    have hempty : ndA5TerminalAtomSourceFinset i = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnotne
    rw [hempty]
    simp [Tao.logFinsetMass]

/-- Denominator-simplified harmonic atom term, with the exact actual-support
selector and the exact physical-band normalizer retained. -/
noncomputable def ndA5HarmonicTerminalAtomIdealMass
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : ℝ :=
  if ndA5TerminalAtomSupported i then
    ((((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
          Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
        (i.2.2.2.1 : ℝ)) /
      Tao.logFinsetMass (ndA5OddBand B branch j))
  else 0

/-- Classifying the actual source finset turns the neutral source-sum ideal
into the explicit residue-and-physical-band supported scalar. -/
theorem ndA5HarmonicTerminalAtomSourceSumIdealMass_eq_supported
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    ndA5HarmonicTerminalAtomSourceSumIdealMass i =
      ndA5HarmonicTerminalAtomIdealMass i := by
  classical
  unfold ndA5HarmonicTerminalAtomSourceSumIdealMass
  rw [ndA5TerminalAtomSourceFinset_eq_ite_supported facts i ht2]
  unfold ndA5HarmonicTerminalAtomIdealMass
  by_cases hsupp : ndA5TerminalAtomSupported i <;> simp [hsupp]

/-- Replacing one supported denominator has exact relative defect `F / M`.
Both sides vanish when the actual physical-band atom is unsupported. -/
theorem ndA5HarmonicTerminalAtomMass_sub_ideal_eq
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    let μ := ndA5HarmonicBandPMF B branch j
      facts.schedule.one_le_B hcount
    (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal -
        ndA5HarmonicTerminalAtomIdealMass i =
      ((Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ) /
        (i.2.2.2.1 : ℝ)) *
        (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal := by
  dsimp only
  rw [← ndA5HarmonicTerminalAtomSourceSumIdealMass_eq_supported
    facts i ht2]
  exact ndA5HarmonicTerminalAtomMass_sub_sourceSumIdeal_eq
    facts.schedule.one_le_B hcount i

/-- Pointwise denominator defect is nonnegative and bounded by the local A5
affine ratio times the actual atom mass. -/
theorem ndA5HarmonicTerminalAtomMass_sub_ideal_nonneg_le
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    let μ := ndA5HarmonicBandPMF B branch j
      facts.schedule.one_le_B hcount
    0 ≤ (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal -
        ndA5HarmonicTerminalAtomIdealMass i ∧
      (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal -
          ndA5HarmonicTerminalAtomIdealMass i ≤
        (B : ℝ) ^ (-(19749 / 20000 : ℝ)) *
          (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal := by
  dsimp only
  rw [ndA5HarmonicTerminalAtomMass_sub_ideal_eq facts hcount i ht2]
  have hratio :=
    ndA5_affineOffset_div_ePrime_le_rpow_neg_19749_div_20000
      facts hlogB (ndA5TerminalAtom_endpoint_mem i) ht2
        (ndA5TerminalAtomValuations_length i)
  have hmassNonneg :
      0 ≤ ((ndA5HarmonicBandPMF B branch j
        facts.schedule.one_le_B hcount).toOuterMeasure
          (ndA5TerminalAtom i)).toReal :=
    ENNReal.toReal_nonneg
  exact ⟨mul_nonneg hratio.1 hmassNonneg,
    mul_le_mul_of_nonneg_right hratio.2 hmassNonneg⟩

/-- Aggregate denominator comparison through the exact disjoint terminal-atom
union mass.  The right side retains that mass rather than an index count. -/
theorem ndA5HarmonicTerminalAtomUnionMass_sub_idealSum_nonneg_le
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C)
    (hpair :
      Set.PairwiseDisjoint
        (Set.univ : Set (NDA5TerminalAtomIndex B branch C j E))
        ndA5TerminalAtom) :
    let μ := ndA5HarmonicBandPMF B branch j
      facts.schedule.one_le_B hcount
    let U := (μ.toOuterMeasure
      (ndA5TerminalAtomUnion B branch C j E)).toReal
    0 ≤ U - ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomIdealMass i ∧
      U - ∑ i : NDA5TerminalAtomIndex B branch C j E,
          ndA5HarmonicTerminalAtomIdealMass i ≤
        (B : ℝ) ^ (-(19749 / 20000 : ℝ)) * U := by
  classical
  dsimp only
  let μ := ndA5HarmonicBandPMF B branch j
    facts.schedule.one_le_B hcount
  have hsum := ndA5TerminalAtomUnion_outerMass_eq_sum μ hpair
  have hpoint := fun i : NDA5TerminalAtomIndex B branch C j E =>
    ndA5HarmonicTerminalAtomMass_sub_ideal_nonneg_le
      facts hlogB hcount i (ht2 i)
  constructor
  · rw [hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _hi => (hpoint i).1
  · calc
      (μ.toOuterMeasure
          (ndA5TerminalAtomUnion B branch C j E)).toReal -
            ∑ i : NDA5TerminalAtomIndex B branch C j E,
              ndA5HarmonicTerminalAtomIdealMass i =
          ∑ i : NDA5TerminalAtomIndex B branch C j E,
            ((μ.toOuterMeasure (ndA5TerminalAtom i)).toReal -
              ndA5HarmonicTerminalAtomIdealMass i) := by
        rw [hsum, Finset.sum_sub_distrib]
      _ ≤ ∑ i : NDA5TerminalAtomIndex B branch C j E,
          (B : ℝ) ^ (-(19749 / 20000 : ℝ)) *
            (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal :=
        Finset.sum_le_sum fun i _hi => (hpoint i).2
      _ = (B : ℝ) ^ (-(19749 / 20000 : ℝ)) *
          ∑ i : NDA5TerminalAtomIndex B branch C j E,
            (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal := by
        rw [Finset.mul_sum]
      _ = (B : ℝ) ^ (-(19749 / 20000 : ℝ)) *
          (μ.toOuterMeasure
            (ndA5TerminalAtomUnion B branch C j E)).toReal := by
        rw [← hsum]

end

end ND
end Erdos1135
