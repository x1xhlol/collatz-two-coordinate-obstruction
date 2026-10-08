import Erdos1135.ND.Band.A5BandPMF
import Erdos1135.ND.Band.A5BandPartition
import Erdos1135.Tao.Probability.LogSupportPerturbation

/-!
# Exact A5 Whole-Source Mixtures

This leaf disintegrates the inclusive A5 source block into its half-open
bands and the possible odd top endpoint.  The endpoint is retained as a raw
restricted submass: it may be empty, so no endpoint PMF is introduced.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The finite carrier of the inclusive A5 source block. -/
abbrev NDA5SourceCarrier
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) :=
  {N : ℕ // N ∈ oddBlock (Tao.taoSection5SourceY B branch)}

/-- Forget the source-block witness while retaining oddness. -/
def ndA5OddBlockValueToOddNat
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} :
    NDA5SourceCarrier B branch → Tao.TaoOddNat :=
  fun N =>
    ⟨N.1, Nat.odd_iff.mpr (by
      simpa only [oddBlock, Tao.taoNyOddWindow] using
        (Tao.oddLogWindow_mem.mp N.2).2.2)⟩

/-- Positive band count supplies a point in the inclusive source block. -/
theorem ndA5OddBlock_sourceY_nonempty
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    (oddBlock (Tao.taoSection5SourceY B branch)).Nonempty := by
  rcases ndA5OddBand_nonempty hB 0 hcount with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  rw [oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
    hB branch hcount]
  exact Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr hcount, hN⟩)

/-- Positive band count also supplies positive logarithmic source mass. -/
theorem logFinsetMass_ndA5OddBlock_sourceY_pos
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    0 < Tao.logFinsetMass
      (oddBlock (Tao.taoSection5SourceY B branch)) := by
  rcases ndA5OddBlock_sourceY_nonempty hB branch hcount with ⟨N, hN⟩
  apply Tao.logFinsetMass_pos_of_mem_pos hN
  have hodd : Odd N := (ndA5OddBlockValueToOddNat
    (⟨N, hN⟩ : NDA5SourceCarrier B branch)).2
  have hmod := Nat.odd_iff.mp hodd
  omega

/-- Whole inclusive source law with uniform counting weights. -/
noncomputable def ndA5FlatSourcePMF
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    PMF Tao.TaoOddNat :=
  (uniformOddBlockPMF (Tao.taoSection5SourceY B branch)
    (ndA5OddBlock_sourceY_nonempty hB branch hcount)).map
      ndA5OddBlockValueToOddNat

/-- Whole inclusive source law with reciprocal weights. -/
noncomputable def ndA5HarmonicSourcePMF
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch) :
    PMF Tao.TaoOddNat :=
  (logOddBlockPMF (Tao.taoSection5SourceY B branch)
    (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount)).map
      ndA5OddBlockValueToOddNat

/-- Natural values selected by an event on Tao's odd-source type. -/
def ndA5OddEventValues (A : Set Tao.TaoOddNat) : Set ℕ :=
  Subtype.val '' A

/-- Restrict a finite natural carrier to an arbitrary ambient event. -/
noncomputable def ndA5RestrictedFinset (S : Finset ℕ) (E : Set ℕ) :
    Finset ℕ := by
  classical
  exact S.filter (fun N => N ∈ E)

theorem taoOddNat_mem_iff_val_mem_ndA5OddEventValues
    (A : Set Tao.TaoOddNat) (N : Tao.TaoOddNat) :
    N ∈ A ↔ N.1 ∈ ndA5OddEventValues A := by
  constructor
  · intro hN
    exact ⟨N, hN, rfl⟩
  · rintro ⟨M, hM, hval⟩
    have hNM : N = M := Subtype.ext hval.symm
    simpa only [hNM] using hM

/-- Filtering the exact source partition gives the arbitrary-event cardinal
numerator identity. -/
theorem card_filter_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) (E : Set ℕ) :
    (ndA5RestrictedFinset
      (oddBlock (Tao.taoSection5SourceY B branch)) E).card =
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        (ndA5RestrictedFinset (ndA5OddBand B branch j) E).card) +
      (ndA5RestrictedFinset (ndA5OddTopEndpoint B branch) E).card := by
  classical
  unfold ndA5RestrictedFinset
  rw [oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
    hB branch hcount, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter
        (ndA5Bands_disjoint_oddRealEndpoint hB hcount)),
    Finset.filter_biUnion,
    Finset.card_biUnion
      (Finset.pairwiseDisjoint_filter
        (ndA5OddBand_pairwiseDisjoint hB branch
          (ndA5BandCount B branch)) _)]

/-- Filtering the exact source partition gives the arbitrary-event
reciprocal-mass numerator identity. -/
theorem logFinsetMass_filter_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) (E : Set ℕ) :
    Tao.logFinsetMass
        (ndA5RestrictedFinset
          (oddBlock (Tao.taoSection5SourceY B branch)) E) =
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        Tao.logFinsetMass
          (ndA5RestrictedFinset (ndA5OddBand B branch j) E)) +
      Tao.logFinsetMass
        (ndA5RestrictedFinset (ndA5OddTopEndpoint B branch) E) := by
  classical
  unfold ndA5RestrictedFinset
  rw [oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
    hB branch hcount]
  unfold Tao.logFinsetMass
  rw [Finset.filter_union,
    Finset.sum_union
      (Finset.disjoint_filter_filter
        (ndA5Bands_disjoint_oddRealEndpoint hB hcount)),
    Finset.filter_biUnion,
    Finset.sum_biUnion
      (Finset.pairwiseDisjoint_filter
        (ndA5OddBand_pairwiseDisjoint hB branch
          (ndA5BandCount B branch)) _)]

private def ndA5SourceEventCarrierEquiv
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (A : Set Tao.TaoOddNat) :
    {N : NDA5SourceCarrier B branch //
      ndA5OddBlockValueToOddNat N ∈ A} ≃
      {N : ℕ // N ∈
        ndA5RestrictedFinset
          (oddBlock (Tao.taoSection5SourceY B branch))
          (ndA5OddEventValues A)} where
  toFun N := ⟨N.1.1, by
    classical
    exact Finset.mem_filter.mpr ⟨N.1.2,
    (taoOddNat_mem_iff_val_mem_ndA5OddEventValues A _).mp N.2⟩⟩
  invFun N :=
    ⟨⟨N.1, by
        classical
        exact (Finset.mem_filter.mp N.2).1⟩,
      (taoOddNat_mem_iff_val_mem_ndA5OddEventValues A _).mpr (by
        classical
        exact (Finset.mem_filter.mp N.2).2)⟩
  left_inv N := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv N := by
    apply Subtype.ext
    rfl

private def ndA5BandEventCarrierEquiv
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (A : Set Tao.TaoOddNat) :
    {N : NDA5BandCarrier B branch j // ndA5BandValueToOddNat N ∈ A} ≃
      {N : ℕ // N ∈
        ndA5RestrictedFinset (ndA5OddBand B branch j)
          (ndA5OddEventValues A)} where
  toFun N := ⟨N.1.1, by
    classical
    exact Finset.mem_filter.mpr ⟨N.1.2,
    (taoOddNat_mem_iff_val_mem_ndA5OddEventValues A _).mp N.2⟩⟩
  invFun N :=
    ⟨⟨N.1, by
        classical
        exact (Finset.mem_filter.mp N.2).1⟩,
      (taoOddNat_mem_iff_val_mem_ndA5OddEventValues A _).mpr (by
        classical
        exact (Finset.mem_filter.mp N.2).2)⟩
  left_inv N := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv N := by
    apply Subtype.ext
    rfl

/-- Exact arbitrary-event ratio for the whole uniform source law. -/
theorem ndA5FlatSourcePMF_eventMass_eq_card_filter_div
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure A).toReal =
      ((ndA5RestrictedFinset
        (oddBlock (Tao.taoSection5SourceY B branch))
        (ndA5OddEventValues A)).card : ℝ) /
      ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
  classical
  rw [ndA5FlatSourcePMF, PMF.toOuterMeasure_map_apply]
  rw [← Tao.pmfProb_eq_toOuterMeasure_toReal]
  let hne := ndA5OddBlock_sourceY_nonempty hB branch hcount
  letI : Nonempty (NDA5SourceCarrier B branch) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  change Tao.pmfProb (PMF.uniformOfFintype (NDA5SourceCarrier B branch))
      (ndA5OddBlockValueToOddNat ⁻¹' A) = _
  rw [Tao.pmfProb_uniformOfFintype]
  have hcard :
      Fintype.card ↑((@ndA5OddBlockValueToOddNat B branch) ⁻¹' A) =
        (ndA5RestrictedFinset
          (oddBlock (Tao.taoSection5SourceY B branch))
          (ndA5OddEventValues A)).card := by
    calc
      Fintype.card ↑((@ndA5OddBlockValueToOddNat B branch) ⁻¹' A) =
          Fintype.card
            {N : NDA5SourceCarrier B branch //
              ndA5OddBlockValueToOddNat N ∈ A} := rfl
      _ = Fintype.card
          {N : ℕ // N ∈
            ndA5RestrictedFinset
              (oddBlock (Tao.taoSection5SourceY B branch))
              (ndA5OddEventValues A)} :=
        Fintype.card_congr (ndA5SourceEventCarrierEquiv A)
      _ = _ := Fintype.card_coe _
  rw [hcard]
  simp only [Fintype.card_coe]

/-- Exact arbitrary-event ratio for one uniform A5 band law. -/
theorem ndA5FlatBandPMF_eventMass_eq_card_filter_div
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal =
      ((ndA5RestrictedFinset (ndA5OddBand B branch j)
        (ndA5OddEventValues A)).card : ℝ) /
      ((ndA5OddBand B branch j).card : ℝ) := by
  classical
  rw [ndA5FlatBandPMF_toOuterMeasure_apply hB hcount]
  rw [← Tao.pmfProb_eq_toOuterMeasure_toReal]
  let hne := ndA5OddBand_nonempty hB j hcount
  letI : Nonempty (NDA5BandCarrier B branch j) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  change Tao.pmfProb (PMF.uniformOfFintype (NDA5BandCarrier B branch j))
      (ndA5BandValueToOddNat ⁻¹' A) = _
  rw [Tao.pmfProb_uniformOfFintype]
  have hcard :
      Fintype.card ↑((@ndA5BandValueToOddNat B branch j) ⁻¹' A) =
        (ndA5RestrictedFinset (ndA5OddBand B branch j)
          (ndA5OddEventValues A)).card := by
    calc
      Fintype.card ↑((@ndA5BandValueToOddNat B branch j) ⁻¹' A) =
          Fintype.card
            {N : NDA5BandCarrier B branch j //
              ndA5BandValueToOddNat N ∈ A} := rfl
      _ = Fintype.card
          {N : ℕ // N ∈
            ndA5RestrictedFinset (ndA5OddBand B branch j)
              (ndA5OddEventValues A)} :=
        Fintype.card_congr (ndA5BandEventCarrierEquiv A)
      _ = _ := Fintype.card_coe _
  rw [hcard]
  simp only [Fintype.card_coe]

/-- Exact arbitrary-event ratio for the whole harmonic source law. -/
theorem ndA5HarmonicSourcePMF_eventMass_eq_logFinsetMass_filter_div
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure A).toReal =
      Tao.logFinsetMass
          (ndA5RestrictedFinset
            (oddBlock (Tao.taoSection5SourceY B branch))
            (ndA5OddEventValues A)) /
        Tao.logFinsetMass
          (oddBlock (Tao.taoSection5SourceY B branch)) := by
  classical
  rw [ndA5HarmonicSourcePMF, PMF.toOuterMeasure_map_apply]
  rw [← Tao.pmfProb_eq_toOuterMeasure_toReal]
  have hpreimage :
      (@ndA5OddBlockValueToOddNat B branch) ⁻¹' A =
        {N : NDA5SourceCarrier B branch |
          N.1 ∈ ndA5OddEventValues A} := by
    ext N
    exact taoOddNat_mem_iff_val_mem_ndA5OddEventValues A _
  rw [hpreimage]
  change Tao.pmfProb
      (Tao.logFinsetPMF
        (oddBlock (Tao.taoSection5SourceY B branch))
        (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount))
      {N : NDA5SourceCarrier B branch |
        N.1 ∈ ndA5OddEventValues A} = _
  rw [Tao.pmfProb_logFinsetPMF]
  simp only [Tao.logFinsetProb, Tao.logFinsetMass,
    ndA5RestrictedFinset]

/-- Exact arbitrary-event ratio for one harmonic A5 band law. -/
theorem ndA5HarmonicBandPMF_eventMass_eq_logFinsetMass_filter_div
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal =
      Tao.logFinsetMass
          (ndA5RestrictedFinset (ndA5OddBand B branch j)
            (ndA5OddEventValues A)) /
        Tao.logFinsetMass (ndA5OddBand B branch j) := by
  classical
  rw [ndA5HarmonicBandPMF_toOuterMeasure_apply hB hcount]
  rw [← Tao.pmfProb_eq_toOuterMeasure_toReal]
  have hpreimage :
      (@ndA5BandValueToOddNat B branch j) ⁻¹' A =
        {N : NDA5BandCarrier B branch j |
          N.1 ∈ ndA5OddEventValues A} := by
    ext N
    exact taoOddNat_mem_iff_val_mem_ndA5OddEventValues A _
  rw [hpreimage]
  change Tao.pmfProb
      (Tao.logFinsetPMF (ndA5OddBand B branch j)
        (logFinsetMass_ndA5OddBand_pos hB j hcount))
      {N : NDA5BandCarrier B branch j |
        N.1 ∈ ndA5OddEventValues A} = _
  rw [Tao.pmfProb_logFinsetPMF]
  simp only [Tao.logFinsetProb, Tao.logFinsetMass,
    ndA5RestrictedFinset]

/-- Flat mixture weight of one half-open band. -/
noncomputable def ndA5FlatBandWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) : ℝ :=
  ((ndA5OddBand B branch j).card : ℝ) /
    ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ)

/-- Harmonic mixture weight of one half-open band. -/
noncomputable def ndA5HarmonicBandWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) : ℝ :=
  Tao.logFinsetMass (ndA5OddBand B branch j) /
    Tao.logFinsetMass (oddBlock (Tao.taoSection5SourceY B branch))

/-- Flat weight of the possible top endpoint. -/
noncomputable def ndA5FlatTopWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : ℝ :=
  ((ndA5OddTopEndpoint B branch).card : ℝ) /
    ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ)

/-- Harmonic weight of the possible top endpoint. -/
noncomputable def ndA5HarmonicTopWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : ℝ :=
  Tao.logFinsetMass (ndA5OddTopEndpoint B branch) /
    Tao.logFinsetMass (oddBlock (Tao.taoSection5SourceY B branch))

/-- Raw flat mass of the part of an event lying at the possible top. -/
noncomputable def ndA5FlatTopRestrictedMass
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (A : Set Tao.TaoOddNat) : ℝ :=
  ((ndA5RestrictedFinset (ndA5OddTopEndpoint B branch)
      (ndA5OddEventValues A)).card : ℝ) /
    ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ)

/-- Raw harmonic mass of the part of an event lying at the possible top. -/
noncomputable def ndA5HarmonicTopRestrictedMass
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (A : Set Tao.TaoOddNat) : ℝ :=
  Tao.logFinsetMass
      (ndA5RestrictedFinset (ndA5OddTopEndpoint B branch)
        (ndA5OddEventValues A)) /
    Tao.logFinsetMass (oddBlock (Tao.taoSection5SourceY B branch))

/-- Every band used by the exact finite mixture lies in the source block. -/
theorem ndA5OddBand_subset_oddBlock_sourceY
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) {j : ℕ}
    (hj : j < ndA5BandCount B branch) :
    ndA5OddBand B branch j ⊆
      oddBlock (Tao.taoSection5SourceY B branch) := by
  intro N hN
  rw [oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
    hB branch hcount]
  exact Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hN⟩)

/-- The flat band weights and raw top weight normalize exactly. -/
theorem sum_ndA5FlatBandWeight_add_topWeight_eq_one
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    (∑ j ∈ Finset.range (ndA5BandCount B branch),
      ndA5FlatBandWeight B branch j) +
        ndA5FlatTopWeight B branch = 1 := by
  have hdecomp :=
    card_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
      hB branch hcount
  have hcast :
      ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) =
        (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ((ndA5OddBand B branch j).card : ℝ)) +
        ((ndA5OddTopEndpoint B branch).card : ℝ) := by
    exact_mod_cast hdecomp
  unfold ndA5FlatBandWeight ndA5FlatTopWeight
  rw [← Finset.sum_div, ← add_div, ← hcast]
  have hcardPos :
      0 < ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (ndA5OddBlock_sourceY_nonempty hB branch hcount)
  exact div_self hcardPos.ne'

/-- The harmonic band weights and raw top weight normalize exactly. -/
theorem sum_ndA5HarmonicBandWeight_add_topWeight_eq_one
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    (∑ j ∈ Finset.range (ndA5BandCount B branch),
      ndA5HarmonicBandWeight B branch j) +
        ndA5HarmonicTopWeight B branch = 1 := by
  unfold ndA5HarmonicBandWeight ndA5HarmonicTopWeight
  rw [← Finset.sum_div, ← add_div,
    ← logFinsetMass_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
      hB branch hcount]
  exact div_self
    (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount).ne'

/-- Exact arbitrary-event disintegration of the whole uniform source law. -/
theorem ndA5FlatSourcePMF_eventMass_eq_band_mixture_add_top
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure A).toReal =
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        ndA5FlatBandWeight B branch j *
          ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal) +
      ndA5FlatTopRestrictedMass B branch A := by
  rw [ndA5FlatSourcePMF_eventMass_eq_card_filter_div hB hcount]
  have hterm : ∀ j ∈ Finset.range (ndA5BandCount B branch),
      ndA5FlatBandWeight B branch j *
          ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal =
        ((ndA5RestrictedFinset (ndA5OddBand B branch j)
          (ndA5OddEventValues A)).card : ℝ) /
        ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    intro j _hj
    rw [ndA5FlatBandPMF_eventMass_eq_card_filter_div hB hcount]
    unfold ndA5FlatBandWeight
    exact div_mul_div_cancel₀'
      (show ((ndA5OddBand B branch j).card : ℝ) ≠ 0 by
        exact_mod_cast (ndA5OddBand_card_pos hB j hcount).ne') _ _
  rw [Finset.sum_congr rfl hterm]
  unfold ndA5FlatTopRestrictedMass
  rw [← Finset.sum_div, ← add_div]
  congr 1
  exact_mod_cast
    card_filter_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
      hB branch hcount (ndA5OddEventValues A)

/-- Exact arbitrary-event disintegration of the whole harmonic source law. -/
theorem ndA5HarmonicSourcePMF_eventMass_eq_band_mixture_add_top
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure A).toReal =
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        ndA5HarmonicBandWeight B branch j *
          ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal) +
      ndA5HarmonicTopRestrictedMass B branch A := by
  rw [ndA5HarmonicSourcePMF_eventMass_eq_logFinsetMass_filter_div
    hB hcount]
  have hterm : ∀ j ∈ Finset.range (ndA5BandCount B branch),
      ndA5HarmonicBandWeight B branch j *
          ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal =
        Tao.logFinsetMass
            (ndA5RestrictedFinset (ndA5OddBand B branch j)
              (ndA5OddEventValues A)) /
          Tao.logFinsetMass
            (oddBlock (Tao.taoSection5SourceY B branch)) := by
    intro j _hj
    rw [ndA5HarmonicBandPMF_eventMass_eq_logFinsetMass_filter_div
      hB hcount]
    unfold ndA5HarmonicBandWeight
    exact div_mul_div_cancel₀'
      (logFinsetMass_ndA5OddBand_pos hB j hcount).ne' _ _
  rw [Finset.sum_congr rfl hterm]
  unfold ndA5HarmonicTopRestrictedMass
  rw [← Finset.sum_div, ← add_div,
    ← logFinsetMass_filter_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
      hB branch hcount (ndA5OddEventValues A)]

/-- The raw flat top contribution is nonnegative. -/
theorem ndA5FlatTopRestrictedMass_nonneg
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    0 ≤ ndA5FlatTopRestrictedMass B branch A := by
  unfold ndA5FlatTopRestrictedMass
  apply div_nonneg (by positivity)
  have hcardPos :
      0 < ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (ndA5OddBlock_sourceY_nonempty hB branch hcount)
  exact hcardPos.le

/-- The raw flat top contribution is bounded by the full top weight. -/
theorem ndA5FlatTopRestrictedMass_le_weight
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ndA5FlatTopRestrictedMass B branch A ≤
      ndA5FlatTopWeight B branch := by
  unfold ndA5FlatTopRestrictedMass ndA5FlatTopWeight
  have hcardPos :
      0 < ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (ndA5OddBlock_sourceY_nonempty hB branch hcount)
  apply div_le_div_of_nonneg_right _ hcardPos.le
  exact_mod_cast Finset.card_le_card
    (show ndA5RestrictedFinset (ndA5OddTopEndpoint B branch)
        (ndA5OddEventValues A) ⊆ ndA5OddTopEndpoint B branch by
      intro N hN
      classical
      exact (Finset.mem_filter.mp hN).1)

/-- The raw harmonic top contribution is nonnegative. -/
theorem ndA5HarmonicTopRestrictedMass_nonneg
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    0 ≤ ndA5HarmonicTopRestrictedMass B branch A := by
  unfold ndA5HarmonicTopRestrictedMass
  exact div_nonneg (Tao.logFinsetMass_nonneg _)
    (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount).le

/-- The raw harmonic top contribution is bounded by the full top weight. -/
theorem ndA5HarmonicTopRestrictedMass_le_weight
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    ndA5HarmonicTopRestrictedMass B branch A ≤
      ndA5HarmonicTopWeight B branch := by
  unfold ndA5HarmonicTopRestrictedMass ndA5HarmonicTopWeight
  apply div_le_div_of_nonneg_right _
    (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount).le
  apply Tao.logFinsetMass_mono
  intro N hN
  classical
  exact (Finset.mem_filter.mp hN).1

/-- Every flat mixture weight is nonnegative. -/
theorem ndA5FlatBandWeight_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    0 ≤ ndA5FlatBandWeight B branch j := by
  unfold ndA5FlatBandWeight
  positivity

/-- Every harmonic mixture weight is nonnegative. -/
theorem ndA5HarmonicBandWeight_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    0 ≤ ndA5HarmonicBandWeight B branch j := by
  unfold ndA5HarmonicBandWeight
  exact div_nonneg (Tao.logFinsetMass_nonneg _)
    (Tao.logFinsetMass_nonneg _)

/-- The flat raw top weight is nonnegative. -/
theorem ndA5FlatTopWeight_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) :
    0 ≤ ndA5FlatTopWeight B branch := by
  unfold ndA5FlatTopWeight
  positivity

/-- The harmonic raw top weight is nonnegative. -/
theorem ndA5HarmonicTopWeight_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) :
    0 ≤ ndA5HarmonicTopWeight B branch := by
  unfold ndA5HarmonicTopWeight
  exact div_nonneg (Tao.logFinsetMass_nonneg _)
    (Tao.logFinsetMass_nonneg _)

/-- Paired public arbitrary-event source disintegration for both genuine
source laws. -/
theorem ndA5SourcePMF_eventMass_eq_band_mixtures_add_top
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (A : Set Tao.TaoOddNat) :
    (((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure A).toReal =
        (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5HarmonicBandWeight B branch j *
            ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure A).toReal) +
        ndA5HarmonicTopRestrictedMass B branch A) ∧
      (((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure A).toReal =
        (∑ j ∈ Finset.range (ndA5BandCount B branch),
          ndA5FlatBandWeight B branch j *
            ((ndA5FlatBandPMF B branch j hB hcount).toOuterMeasure A).toReal) +
        ndA5FlatTopRestrictedMass B branch A) := by
  exact
    ⟨ndA5HarmonicSourcePMF_eventMass_eq_band_mixture_add_top hB hcount A,
      ndA5FlatSourcePMF_eventMass_eq_band_mixture_add_top hB hcount A⟩

/-- The whole logarithmic source mass retains the zeroth band's uniform
quarter-mass floor. -/
theorem one_fourth_le_logFinsetMass_ndA5OddBlock_sourceY
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    (1 / 4 : ℝ) ≤
      Tao.logFinsetMass
        (oddBlock (Tao.taoSection5SourceY B branch)) := by
  calc
    (1 / 4 : ℝ) ≤ Tao.logFinsetMass (ndA5OddBand B branch 0) :=
      one_fourth_le_logFinsetMass_ndA5OddBand hB 0 hcount
    _ ≤ Tao.logFinsetMass
        (oddBlock (Tao.taoSection5SourceY B branch)) :=
      Tao.logFinsetMass_mono
        (ndA5OddBand_subset_oddBlock_sourceY hB hcount hcount)

/-- The possible top has flat weight at most `4/B`. -/
theorem ndA5FlatTopWeight_le_four_div
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5FlatTopWeight B branch ≤ 4 / (B : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (zero_lt_one.trans_le hB)
  have hYgeB :
      (B : ℝ) ≤ Tao.taoSection5SourceY B branch := by
    simpa only [ndA5BandLower_zero] using
      (cast_le_ndA5BandLower hB branch 0)
  have hYpos : 0 < Tao.taoSection5SourceY B branch :=
    hBpos.trans_le hYgeB
  have hmassUpper :
      Tao.logFinsetMass (ndA5OddBand B branch 0) ≤
        ((ndA5OddBand B branch 0).card : ℝ) /
          Tao.taoSection5SourceY B branch := by
    simpa only [ndA5BandLower_zero] using
      (logFinsetMass_ndA5OddBand_le_card_div_lower
        hB 0 hcount)
  have hquarterDiv :
      (1 / 4 : ℝ) ≤
        ((ndA5OddBand B branch 0).card : ℝ) /
          Tao.taoSection5SourceY B branch :=
    (one_fourth_le_logFinsetMass_ndA5OddBand hB 0 hcount).trans
      hmassUpper
  have hquarterY :
      (1 / 4 : ℝ) * Tao.taoSection5SourceY B branch ≤
        ((ndA5OddBand B branch 0).card : ℝ) :=
    (le_div_iff₀ hYpos).mp hquarterDiv
  have hbandSourceCard :
      (ndA5OddBand B branch 0).card ≤
        (oddBlock (Tao.taoSection5SourceY B branch)).card :=
    Finset.card_le_card
      (ndA5OddBand_subset_oddBlock_sourceY hB hcount hcount)
  have hbandSourceCardReal :
      ((ndA5OddBand B branch 0).card : ℝ) ≤
        ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    exact_mod_cast hbandSourceCard
  have hBsource :
      (B : ℝ) ≤
        4 * ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    nlinarith
  have htop :
      ((ndA5OddTopEndpoint B branch).card : ℝ) ≤ 1 := by
    exact_mod_cast card_oddRealEndpoint_le_one
      (Real.rpow (Tao.taoSection5SourceY B branch) alpha)
  have hsourceCardPos :
      0 < ((oddBlock (Tao.taoSection5SourceY B branch)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (ndA5OddBlock_sourceY_nonempty hB branch hcount)
  unfold ndA5FlatTopWeight
  apply (div_le_div_iff₀ hsourceCardPos hBpos).2
  have htopMul :
      ((ndA5OddTopEndpoint B branch).card : ℝ) * (B : ℝ) ≤ B := by
    nlinarith
  exact htopMul.trans hBsource

/-- The possible top has harmonic weight at most `4/B`. -/
theorem ndA5HarmonicTopWeight_le_four_div
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5HarmonicTopWeight B branch ≤ 4 / (B : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (zero_lt_one.trans_le hB)
  have hYgeB :
      (B : ℝ) ≤ Tao.taoSection5SourceY B branch := by
    simpa only [ndA5BandLower_zero] using
      (cast_le_ndA5BandLower hB branch 0)
  have hYone : (1 : ℝ) ≤ Tao.taoSection5SourceY B branch :=
    (show (1 : ℝ) ≤ B by exact_mod_cast hB).trans hYgeB
  have hYpos : 0 < Tao.taoSection5SourceY B branch :=
    zero_lt_one.trans_le hYone
  have hYu :
      Tao.taoSection5SourceY B branch ≤
        Real.rpow (Tao.taoSection5SourceY B branch) alpha :=
    Real.self_le_rpow_of_one_le hYone (by
      norm_num [alpha, Tao.taoAlpha])
  have huPos :
      0 < Real.rpow (Tao.taoSection5SourceY B branch) alpha :=
    Real.rpow_pos_of_pos hYpos _
  have hBu :
      (B : ℝ) ≤ Real.rpow (Tao.taoSection5SourceY B branch) alpha :=
    hYgeB.trans hYu
  have htopU :
      Tao.logFinsetMass (ndA5OddTopEndpoint B branch) ≤
        1 / Real.rpow (Tao.taoSection5SourceY B branch) alpha := by
    unfold ndA5OddTopEndpoint
    exact logFinsetMass_oddRealEndpoint_le_one_div huPos
  have htopB :
      Tao.logFinsetMass (ndA5OddTopEndpoint B branch) ≤
        1 / (B : ℝ) :=
    htopU.trans (one_div_le_one_div_of_le hBpos hBu)
  have hsourcePos :=
    logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount
  have hsourceQuarter :=
    one_fourth_le_logFinsetMass_ndA5OddBlock_sourceY hB branch hcount
  unfold ndA5HarmonicTopWeight
  calc
    Tao.logFinsetMass (ndA5OddTopEndpoint B branch) /
          Tao.logFinsetMass
            (oddBlock (Tao.taoSection5SourceY B branch))
        ≤ (1 / (B : ℝ)) /
            Tao.logFinsetMass
              (oddBlock (Tao.taoSection5SourceY B branch)) :=
      div_le_div_of_nonneg_right htopB hsourcePos.le
    _ = 1 / ((B : ℝ) *
          Tao.logFinsetMass
            (oddBlock (Tao.taoSection5SourceY B branch))) := by
      rw [div_div]
    _ ≤ 4 / (B : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hBpos hsourcePos) hBpos).2
      nlinarith

end

end ND
end Erdos1135
