import Erdos1135.Tao.Section5.PassTimeLocalization
import Erdos1135.Tao.Section5.PassLostWindow
import Erdos1135.Tao.Section5.AffineAtomReverse
import Erdos1135.Tao.Section5.PassTypicalEvent

/-!
# Section 5 Deterministic Pass-Event Partition

This leaf brackets the closed-good repaired-interior passage event by the
finite union of scheduled affine atoms and the unrestricted passage event.
It also proves the atom family is pairwise disjoint. Probability estimates,
source-boundary loss, and atom-mass formulas remain outside this module.
-/

namespace Erdos1135
namespace Tao

open Filter

noncomputable section

/-- Eventual deterministic facts used by both directions of the atom
partition. -/
structure TaoSection5PassEventPartitionFacts (B : ℕ) : Prop where
  geometry : TaoSection5PowerInteriorFacts B
  time : TaoSection5PassTimeLocalizationFacts B
  lost : TaoSection5PassLostWindowFacts B
  reverseBudget : taoSection5ReversePrefixScalarBudget B

theorem eventually_taoSection5PassEventPartitionFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PassEventPartitionFacts B := by
  filter_upwards
    [eventually_taoSection5PowerInteriorFacts,
      eventually_taoSection5PassTimeLocalizationFacts,
      eventually_taoSection5PassLostWindowFacts,
      eventually_taoSection5ReversePrefixScalarBudget]
      with B geometry time lost reverseBudget
  exact ⟨geometry, time, lost, reverseBudget⟩

/-- Odd sources whose orbit first enters `[0,B]` at some time and lands in
`E`. No artificial no-hit value is present. -/
def taoSection5PassEvent (B : ℕ) (E : Set ℕ) : Set TaoOddNat :=
  {N | ∃ n, taoSection5PassEventAtTime B N.1 n E}

@[simp] theorem taoSection5PassEvent_empty (B : ℕ) :
    taoSection5PassEvent B ∅ = ∅ := by
  ext N
  simp [taoSection5PassEvent, taoSection5PassEventAtTime]

/-- Repaired source interior for one Section 5 branch. -/
def taoSection5PowerInteriorEvent
    (B : ℕ) (branch : TaoSection5SourceBranch) : Set TaoOddNat :=
  {N | N.1 ∈ taoSection5PowerInterior B branch}

/-- The left-hand gated passage event in the deterministic sandwich. -/
def taoSection5ClosedGoodInteriorPassEvent
    (B : ℕ) (branch : TaoSection5SourceBranch) (E : Set ℕ) : Set TaoOddNat :=
  taoSection5PassEvent B E ∩ taoSection5ClosedGoodEvent B ∩
    taoSection5PowerInteriorEvent B branch

/-- Strict source-facing version of the left-hand gated passage event. -/
def taoSection5SourceTypicalInteriorPassEvent
    (B : ℕ) (branch : TaoSection5SourceBranch) (E : Set ℕ) : Set TaoOddNat :=
  taoSection5PassEvent B E ∩ taoSection5SourceTypicalEvent B ∩
    taoSection5PowerInteriorEvent B branch

theorem taoSection5SourceTypicalInteriorPassEvent_subset_closedGood
    (B : ℕ) (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    taoSection5SourceTypicalInteriorPassEvent B branch E ⊆
      taoSection5ClosedGoodInteriorPassEvent B branch E := by
  rintro N ⟨⟨hpass, htyp⟩, hinterior⟩
  exact
    ⟨⟨hpass, taoSection5SourceTypicalEvent_subset_closedGoodEvent B htyp⟩,
      hinterior⟩

/-- The finite dependent index of scheduled times, closed-typical tuples at
the shifted horizon, and endpoints in the common target `EPrime`. -/
abbrev TaoSection5ClosedAffineAtomIndex
    (B : ℕ) (branch : TaoSection5SourceBranch) (E : Set ℕ) :=
  Σ n : {n // n ∈ taoSection5PassTimes B branch},
    {as // as ∈ taoSection5TypicalTuples B (n.1 - taoSection5M0 B)} ×
      {M // M ∈ taoSection5EPrime B E}

noncomputable instance taoSection5ClosedAffineAtomIndexFintype
    (B : ℕ) (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    Fintype (TaoSection5ClosedAffineAtomIndex B branch E) := by
  classical
  unfold TaoSection5ClosedAffineAtomIndex
  infer_instance

/-- The source fiber of one scheduled closed affine atom. -/
def taoSection5ClosedAffineAtom
    {B : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    (i : TaoSection5ClosedAffineAtomIndex B branch E) : Set TaoOddNat :=
  {N | taoAffList i.2.1.1 (N.1 : ℚ) = (i.2.2.1 : ℚ)}

/-- Union of all scheduled closed affine atoms for a fixed source branch and
target event. -/
def taoSection5ClosedAffineAtomUnion
    (B : ℕ) (branch : TaoSection5SourceBranch) (E : Set ℕ) : Set TaoOddNat :=
  ⋃ i : TaoSection5ClosedAffineAtomIndex B branch E,
    taoSection5ClosedAffineAtom i

@[simp] theorem taoSection5ClosedAffineAtomUnion_empty
    (B : ℕ) (branch : TaoSection5SourceBranch) :
    taoSection5ClosedAffineAtomUnion B branch ∅ = ∅ := by
  ext N
  simp [taoSection5ClosedAffineAtomUnion, taoSection5ClosedAffineAtom,
    TaoSection5ClosedAffineAtomIndex, taoSection5EPrime_empty]

private theorem TaoSection5TypicalTuple.actual_prefix_partition
    {B r N : ℕ} (hN : Odd N)
    (htyp : taoSection5TypicalTuple B r
      (syracuseValuationPNatList r N hN))
    {j : ℕ} (hj : j ≤ r) :
    taoSection5TypicalTuple B j
      (syracuseValuationPNatList j N hN) := by
  have htake := TaoSection5TypicalTuple.take htyp hj
  simpa only [syracuseValuationPNatList_take_of_le hN hj] using htake

/-- Every closed-good repaired-interior passage event supplies a scheduled
closed affine atom. -/
theorem taoSection5ClosedGoodInteriorPassEvent_subset_atomUnion
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    taoSection5ClosedGoodInteriorPassEvent B branch E ⊆
      taoSection5ClosedAffineAtomUnion B branch E := by
  rintro N ⟨⟨⟨n, hpass⟩, hgood⟩, hinterior⟩
  have hn : n ∈ taoSection5PassTimes B branch :=
    taoSection5_firstHit_mem_passTimes facts.geometry facts.time N.2
      hinterior hgood hpass.1
  have hn0 : n ≤ taoSection5N0 B :=
    (facts.geometry.schedule.range branch n hn).2
  have htypN :
      taoSection5TypicalTuple B n
        (syracuseValuationPNatList n N.1 N.2) :=
    TaoSection5TypicalTuple.actual_prefix_partition N.2 hgood hn0
  have hm : taoSection5M0 B ≤ n :=
    facts.geometry.schedule.m0_le hn
  let r := n - taoSection5M0 B
  let as := syracuseValuationPNatList r N.1 N.2
  let M := (syracuse^[r]) N.1
  have hr0 : r ≤ taoSection5N0 B := by
    simpa only [r] using facts.geometry.schedule.sub_le_n0 hn
  have htypR : taoSection5TypicalTuple B r as := by
    simpa only [as] using
      TaoSection5TypicalTuple.actual_prefix_partition N.2 hgood hr0
  have has : as ∈ taoSection5TypicalTuples B r :=
    mem_taoSection5TypicalTuples_iff.mpr htypR
  have hM : M ∈ taoSection5EPrime B E := by
    simpa only [r, M] using
      taoSection5PassEvent_shifted_mem_EPrime
        facts.lost N.2 hm htypN hpass
  have hAff : taoAffList as (N.1 : ℚ) = (M : ℚ) := by
    dsimp only [as, M]
    exact (syracuse_iterate_eq_taoAffList r N.1 N.2).symm
  let i : TaoSection5ClosedAffineAtomIndex B branch E :=
    ⟨⟨n, hn⟩, ⟨⟨as, has⟩, ⟨M, hM⟩⟩⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  exact hAff

/-- Every scheduled closed affine atom reconstructs a genuine passage event. -/
theorem taoSection5ClosedAffineAtomUnion_subset_passEvent
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    taoSection5ClosedAffineAtomUnion B branch E ⊆
      taoSection5PassEvent B E := by
  intro N hN
  rcases Set.mem_iUnion.mp hN with ⟨i, hi⟩
  refine ⟨i.1.1, ?_⟩
  exact taoSection5PassEventAtTime_of_scheduledAffineAtom
    facts.geometry.schedule i.1.2 i.2.1.2 i.2.2.2 hi
      facts.reverseBudget

/-- The checked deterministic sandwich. The right event is deliberately the
full genuine passage event rather than an unconditional atom equality. -/
theorem taoSection5_closedGoodInterior_atomUnion_sandwich
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    taoSection5ClosedGoodInteriorPassEvent B branch E ⊆
        taoSection5ClosedAffineAtomUnion B branch E ∧
      taoSection5ClosedAffineAtomUnion B branch E ⊆
        taoSection5PassEvent B E :=
  ⟨taoSection5ClosedGoodInteriorPassEvent_subset_atomUnion facts branch E,
    taoSection5ClosedAffineAtomUnion_subset_passEvent facts branch E⟩

/-- Source-facing four-stage sandwich from Tao's strict event through the
closed enlargement and finite atom union to the full genuine passage event. -/
theorem taoSection5_sourceTypical_closed_atomUnion_sandwich
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    taoSection5SourceTypicalInteriorPassEvent B branch E ⊆
        taoSection5ClosedGoodInteriorPassEvent B branch E ∧
      taoSection5ClosedGoodInteriorPassEvent B branch E ⊆
          taoSection5ClosedAffineAtomUnion B branch E ∧
        taoSection5ClosedAffineAtomUnion B branch E ⊆
          taoSection5PassEvent B E :=
  ⟨taoSection5SourceTypicalInteriorPassEvent_subset_closedGood B branch E,
    taoSection5_closedGoodInterior_atomUnion_sandwich facts branch E⟩

/-- Two atom witnesses containing the same odd source have identical
scheduled time, tuple, and endpoint. -/
theorem taoSection5ClosedAffineAtomIndex_eq_of_common_mem
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    {branch : TaoSection5SourceBranch} {E : Set ℕ}
    {i j : TaoSection5ClosedAffineAtomIndex B branch E} {N : TaoOddNat}
    (hi : N ∈ taoSection5ClosedAffineAtom i)
    (hj : N ∈ taoSection5ClosedAffineAtom j) :
    i = j := by
  rcases i with ⟨⟨n, hn⟩, ⟨⟨as, has⟩, ⟨M, hM⟩⟩⟩
  rcases j with ⟨⟨n', hn'⟩, ⟨⟨as', has'⟩, ⟨M', hM'⟩⟩⟩
  have hpass := taoSection5PassEventAtTime_of_scheduledAffineAtom
    facts.geometry.schedule hn has hM hi facts.reverseBudget
  have hpass' := taoSection5PassEventAtTime_of_scheduledAffineAtom
    facts.geometry.schedule hn' has' hM' hj facts.reverseBudget
  have hnn' : n = n' :=
    syracuseFirstHitAtMost_unique hpass.1 hpass'.1
  subst n'
  have htyp := mem_taoSection5TypicalTuples_iff.mp has
  have htyp' := mem_taoSection5TypicalTuples_iff.mp has'
  have hModd : Odd M := (mem_taoSection5EPrime_iff.mp hM).2.2.1
  have hM'odd : Odd M' := (mem_taoSection5EPrime_iff.mp hM').2.2.1
  have hdecode := (taoAffList_eq_oddNat_iff as N.2 hModd).mp hi
  have hdecode' := (taoAffList_eq_oddNat_iff as' N.2 hM'odd).mp hj
  have hasas' : as = as' := by
    calc
      as = syracuseValuationPNatList as.length N.1 N.2 := hdecode.1.symm
      _ = syracuseValuationPNatList as'.length N.1 N.2 := by
        rw [htyp.1, htyp'.1]
      _ = as' := hdecode'.1
  subst as'
  have hMM'rat : (M : ℚ) = (M' : ℚ) := by
    calc
      (M : ℚ) = taoAffList as (N.1 : ℚ) := hi.symm
      _ = (M' : ℚ) := hj
  have hMM' : M = M' := by exact_mod_cast hMM'rat
  subst M'
  rfl

/-- The finite scheduled atom family is pairwise disjoint on odd sources. -/
theorem taoSection5ClosedAffineAtoms_pairwiseDisjoint
    {B : ℕ} (facts : TaoSection5PassEventPartitionFacts B)
    (branch : TaoSection5SourceBranch) (E : Set ℕ) :
    Set.PairwiseDisjoint
      (Set.univ : Set (TaoSection5ClosedAffineAtomIndex B branch E))
      taoSection5ClosedAffineAtom := by
  intro i _ j _ hij
  change Disjoint (taoSection5ClosedAffineAtom i)
    (taoSection5ClosedAffineAtom j)
  rw [Set.disjoint_left]
  intro N hi hj
  exact hij (taoSection5ClosedAffineAtomIndex_eq_of_common_mem facts hi hj)

end

end Tao
end Erdos1135
