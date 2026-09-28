import Erdos1135.ND.Band.A5BandPMF
import Erdos1135.ND.Band.A5TerminalAtoms
import Erdos1135.Tao.Probability.GatedSubmassPartition

/-!
# A5 Actual Terminal-Atom Mass

This leaf evaluates the actual physical-band terminal atoms under the exact
flat and harmonic band laws.  It also packages finite additivity for the
already checked disjoint atom family.  No compatibility reduction,
denominator replacement, or support nominalization occurs here.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- Natural sources in the physical band that solve one terminal atom's
exact affine equation. -/
noncomputable def ndA5TerminalAtomSourceFinset
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : Finset ℕ :=
  (ndA5OddBand B branch j).filter fun N =>
    Tao.taoAffList (ndA5TerminalAtomValuations i) (N : ℚ) =
      (i.2.2.2.1 : ℚ)

@[simp] theorem mem_ndA5TerminalAtomSourceFinset_iff
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j N : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    N ∈ ndA5TerminalAtomSourceFinset i ↔
      N ∈ ndA5OddBand B branch j ∧
        Tao.taoAffList (ndA5TerminalAtomValuations i) (N : ℚ) =
          (i.2.2.2.1 : ℚ) := by
  simp [ndA5TerminalAtomSourceFinset]

@[simp] theorem ndA5BandValueToOddNat_mem_terminalAtom_iff
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (N : NDA5BandCarrier B branch j) :
    ndA5BandValueToOddNat N ∈ ndA5TerminalAtom i ↔
      N.1 ∈ ndA5TerminalAtomSourceFinset i := by
  rw [mem_ndA5TerminalAtomSourceFinset_iff]
  change N.1 ∈ ndA5OddBand B branch j ∧
      Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
        (i.2.2.2.1 : ℚ) ↔ _
  rfl

private noncomputable def ndA5TerminalAtomCarrierEquivSource
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    {N : NDA5BandCarrier B branch j //
        ndA5BandValueToOddNat N ∈ ndA5TerminalAtom i} ≃
      {N : ℕ // N ∈ ndA5TerminalAtomSourceFinset i} where
  toFun N :=
    ⟨N.1.1,
      (ndA5BandValueToOddNat_mem_terminalAtom_iff i N.1).mp N.2⟩
  invFun N :=
    ⟨⟨N.1, (mem_ndA5TerminalAtomSourceFinset_iff i).mp N.2 |>.1⟩,
      (ndA5BandValueToOddNat_mem_terminalAtom_iff i _).mpr N.2⟩
  left_inv N := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv N := by
    apply Subtype.ext
    rfl

/-- Exact cardinality-ratio mass of one actual terminal atom under the flat
band law. -/
theorem ndA5FlatBandPMF_terminalAtomMass_eq_card_div
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E) :
    ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5TerminalAtom i)).toReal =
      ((ndA5TerminalAtomSourceFinset i).card : ℝ) /
        ((ndA5OddBand B branch j).card : ℝ) := by
  classical
  rw [ndA5FlatBandPMF_toOuterMeasure_apply hB hcount]
  rw [← Tao.pmfProb_eq_toOuterMeasure_toReal]
  let hne := ndA5OddBand_nonempty hB j hcount
  letI : Nonempty (NDA5BandCarrier B branch j) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  change Tao.pmfProb (PMF.uniformOfFintype (NDA5BandCarrier B branch j))
      (ndA5BandValueToOddNat ⁻¹' ndA5TerminalAtom i) = _
  rw [Tao.pmfProb_uniformOfFintype]
  have hcard :
      Fintype.card
          ↑((@ndA5BandValueToOddNat B branch j) ⁻¹'
            ndA5TerminalAtom i) =
        (ndA5TerminalAtomSourceFinset i).card := by
    calc
      Fintype.card
          ↑((@ndA5BandValueToOddNat B branch j) ⁻¹'
            ndA5TerminalAtom i) =
        Fintype.card
          {N : NDA5BandCarrier B branch j //
            ndA5BandValueToOddNat N ∈ ndA5TerminalAtom i} := rfl
      _ = Fintype.card
          {N : ℕ // N ∈ ndA5TerminalAtomSourceFinset i} :=
        Fintype.card_congr (ndA5TerminalAtomCarrierEquivSource i)
      _ = (ndA5TerminalAtomSourceFinset i).card :=
        Fintype.card_coe _
  rw [hcard]
  simp only [Fintype.card_coe]

/-- Exact logarithmic-mass ratio of one actual terminal atom under the
harmonic band law. -/
theorem ndA5HarmonicBandPMF_terminalAtomMass_eq_logFinsetMass_div
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E) :
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5TerminalAtom i)).toReal =
      Tao.logFinsetMass (ndA5TerminalAtomSourceFinset i) /
        Tao.logFinsetMass (ndA5OddBand B branch j) := by
  classical
  rw [ndA5HarmonicBandPMF_toOuterMeasure_apply hB hcount]
  rw [← Tao.pmfProb_eq_toOuterMeasure_toReal]
  let S := ndA5OddBand B branch j
  let A := ndA5TerminalAtomSourceFinset i
  have hmass : 0 < Tao.logFinsetMass S := by
    simpa only [S] using logFinsetMass_ndA5OddBand_pos hB j hcount
  have hpreimage :
      (@ndA5BandValueToOddNat B branch j) ⁻¹'
          ndA5TerminalAtom i =
        {N : NDA5BandCarrier B branch j | N.1 ∈ A} := by
    ext N
    simpa only [Set.mem_preimage, Set.mem_setOf_eq, A] using
      ndA5BandValueToOddNat_mem_terminalAtom_iff i N
  rw [hpreimage]
  change Tao.pmfProb (Tao.logFinsetPMF S hmass)
      {N : {n : ℕ // n ∈ S} | N.1 ∈ (A : Set ℕ)} = _
  rw [Tao.pmfProb_logFinsetPMF]
  simp only [Tao.logFinsetProb, Tao.logFinsetMass, A, S,
    ndA5TerminalAtomSourceFinset]
  congr 1
  congr 1
  ext N
  simp

private theorem ndA5TerminalAtomUnion_outerMeasure_eq_sum
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (p : PMF Tao.TaoOddNat)
    (hpair :
      Set.PairwiseDisjoint
        (Set.univ : Set (NDA5TerminalAtomIndex B branch C j E))
        ndA5TerminalAtom) :
    p.toOuterMeasure (ndA5TerminalAtomUnion B branch C j E) =
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        p.toOuterMeasure (ndA5TerminalAtom i) := by
  classical
  let I := NDA5TerminalAtomIndex B branch C j E
  let F : I → Set Tao.TaoOddNat := fun i => ndA5TerminalAtom i
  have hpairFin :
      Set.PairwiseDisjoint ((Finset.univ : Finset I) : Set I) F := by
    simpa only [I, F, Finset.coe_univ] using hpair
  have houter :
      p.toOuterMeasure (⋃ i : I, F i) =
        ∑ i : I, p.toOuterMeasure (F i) := by
    simpa using
      Tao.taoPMFToOuterMeasure_biUnion_finset_eq_sum
        p (Finset.univ : Finset I) F hpairFin
  simpa only [ndA5TerminalAtomUnion, I, F] using houter

/-- Real finite additivity for any PMF over a supplied pairwise-disjoint
actual terminal-atom family. -/
theorem ndA5TerminalAtomUnion_outerMass_eq_sum
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (p : PMF Tao.TaoOddNat)
    (hpair :
      Set.PairwiseDisjoint
        (Set.univ : Set (NDA5TerminalAtomIndex B branch C j E))
        ndA5TerminalAtom) :
    (p.toOuterMeasure
        (ndA5TerminalAtomUnion B branch C j E)).toReal =
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        (p.toOuterMeasure (ndA5TerminalAtom i)).toReal := by
  rw [ndA5TerminalAtomUnion_outerMeasure_eq_sum p hpair]
  rw [ENNReal.toReal_sum]
  intro i _hi
  apply ne_of_lt
  calc
    p.toOuterMeasure (ndA5TerminalAtom i) ≤
        p.toOuterMeasure Set.univ :=
      p.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2
      (Set.subset_univ _)
    _ < ⊤ := ENNReal.one_lt_top

end

end ND
end Erdos1135
