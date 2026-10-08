import Erdos1135.ND.Band.A5ShiftedRawComparison
import Erdos1135.ND.Band.A5TwoProfileRawQ
import Erdos1135.ND.Discrepancy.A5TwoProfileTail

/-!
# A5 Actual-Band Reciprocal Two-Profile Consumer

This leaf consumes the checked raw first-shift L1 seam without introducing a
shifted normalizer.  The exact two-cell raw census is split into the checked
base open-lattice profile plus one `(q_(A+1) - q_A)` correction.  Small generic
adapters extend the zero-supported base carrier and rescale normalized base
profile estimates by its own raw mass `Z_A`.
-/

open scoped BigOperators
open AddCircle

namespace Erdos1135
namespace ND

noncomputable section

/-- The exact unweighted two-cell raw census is the base open-lattice profile
plus one strictly gated neighboring-profile error.  Equality at the threshold
keeps the upper cell inactive. -/
theorem sum_ndA5NominalStrictBandRawQ_eq_baseOpen_add_shiftError
    {B nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {A W : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    (∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandRawQTerm B branch A W nu r) =
      ndA5RawQ A W nu *
          ndA5OpenLatticeCount (ndA5BandBeta B branch)
            (Int.fract (A + (nu : ℝ) * logTwoThree)) +
        (ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu) *
          (if ndA5BandTailThreshold B branch <
              Int.fract (A + (nu : ℝ) * logTwoThree)
           then (1 : ℝ) else 0) := by
  let t := Int.fract (A + (nu : ℝ) * logTwoThree)
  have ht : t ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [sum_ndA5NominalStrictBandRawQ_eq_base_add_firstShift hB hlogB]
  rw [ndA5OpenLatticeCount_actualBand_eq_one_add_tail hB hlogB ht]
  by_cases htail : ndA5BandTailThreshold B branch < t
  · simp [t, htail]
    ring
  · simp [t, htail]

/-- Extending a base raw-profile sum to the union with any second full tube
does not change it: the base raw profile is zero off its own carrier. -/
theorem sum_ndA5RawQ_mul_fullTube_union_eq
    (A A' W : ℝ) (F : ℕ → ℝ) :
    (∑ nu ∈ ndA5FullTube A W ∪ ndA5FullTube A' W,
      ndA5RawQ A W nu * F nu) =
      ∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu * F nu := by
  classical
  have hsubset : ndA5FullTube A W ⊆
      ndA5FullTube A W ∪ ndA5FullTube A' W :=
    Finset.subset_union_left
  have hsum :
      (∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu * F nu) =
        ∑ nu ∈ ndA5FullTube A W ∪ ndA5FullTube A' W,
          ndA5RawQ A W nu * F nu := by
    apply Finset.sum_subset hsubset
    intro nu _hnuUnion hnuBase
    rw [ndA5RawQ_of_not_mem hnuBase, zero_mul]
  exact hsum.symm

/-- Positive base tube mass restores a raw atom from its normalized weight. -/
theorem ndA5TubeRawMass_mul_normalizedQ_eq_rawQ_of_pos
    {A W : ℝ} {nu : ℕ} (hZ : 0 < ndA5TubeRawMass A W) :
    ndA5TubeRawMass A W * ndA5NormalizedQ A W nu =
      ndA5RawQ A W nu := by
  unfold ndA5NormalizedQ
  field_simp [hZ.ne']

/-- A normalized base-profile estimate rescales to the corresponding raw
estimate with exactly one factor of the base mass. -/
theorem abs_sum_ndA5RawQ_mul_sub_mass_mul_le_of_normalized
    {A W : ℝ} (F : ℕ → ℝ) (mu E : ℝ)
    (hZ : 0 < ndA5TubeRawMass A W)
    (hNorm :
      |(∑ nu ∈ ndA5FullTube A W,
          ndA5NormalizedQ A W nu * F nu) - mu| ≤ E) :
    |(∑ nu ∈ ndA5FullTube A W,
        ndA5RawQ A W nu * F nu) -
      ndA5TubeRawMass A W * mu| ≤
      ndA5TubeRawMass A W * E := by
  have hsum :
      (∑ nu ∈ ndA5FullTube A W, ndA5RawQ A W nu * F nu) =
        ndA5TubeRawMass A W *
          ∑ nu ∈ ndA5FullTube A W,
            ndA5NormalizedQ A W nu * F nu := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro nu _hnu
    rw [← ndA5TubeRawMass_mul_normalizedQ_eq_rawQ_of_pos hZ]
    ring
  rw [hsum, ← mul_sub, abs_mul, abs_of_pos hZ]
  exact mul_le_mul_of_nonneg_left hNorm hZ.le

/-- The checked normalized open-lattice endpoint lifted to the raw base
carrier.  No shifted mass or shifted normalization appears. -/
theorem abs_sum_ndA5RawQ_mul_openLattice_sub_mass_mul_mean_le_of_analytic
    {B : ℕ} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (phi : UnitAddCircle) (b : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 2) :
    |(∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
        ndA5RawQ A (ndA5TubeWidth B C) nu *
          ndA5OpenLatticeCount b
            (ndUnitRep (ndPhaseOrbit phi nu))) -
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        (b / Real.log 2)| ≤
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        (ndEndpointDbar c kappa
            (ndA5FullTube A (ndA5TubeWidth B C)).card *
          (64 *
            ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
            ndA5TubeWidth B C /
              (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ))) := by
  have hfloor :
      (1 / 32 : ℝ) ≤
        ndA5TubeRawMass A (ndA5TubeWidth B C) :=
    one_div_thirty_two_le_ndA5TubeRawMass_of_analytic hTube
  have hZ : 0 < ndA5TubeRawMass A (ndA5TubeWidth B C) := by
    linarith
  apply abs_sum_ndA5RawQ_mul_sub_mass_mul_le_of_normalized
    (F := fun nu => ndA5OpenLatticeCount b
      (ndUnitRep (ndPhaseOrbit phi nu)))
    (mu := b / Real.log 2)
    (E := ndEndpointDbar c kappa
        (ndA5FullTube A (ndA5TubeWidth B C)).card *
      (64 *
        ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
        ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ))) hZ
  exact abs_sum_ndA5NormalizedQ_mul_openLattice_sub_mean_le_of_analytic
    hPhase hTube phi b hb

/-- Terminal raw reciprocal endpoint for the actual two-cell band.  The base
open profile is paid after one `Z_A` rescaling, and the neighboring-profile
correction is paid once by the checked raw L1 estimate. -/
theorem abs_sum_ndA5NominalStrictBandRawQ_sub_mass_mul_mean_le_of_analytic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube0 : NDA5AnalyticTubeFacts B C A)
    (hTube1 : NDA5AnalyticTubeFacts B C (A + 1)) :
    |(∑ nu ∈
        ndA5FullTube A (ndA5TubeWidth B C) ∪
          ndA5FullTube (A + 1) (ndA5TubeWidth B C),
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch A
            (ndA5TubeWidth B C) nu r) -
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        (ndA5BandBeta B branch / Real.log 2)| ≤
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        (ndEndpointDbar c kappa
            (ndA5FullTube A (ndA5TubeWidth B C)).card *
          (64 *
            ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
            ndA5TubeWidth B C /
              (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ))) +
        (2 * (ndA5TubeWidth B C /
            (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) *
          ndA5TubeRawMass A (ndA5TubeWidth B C) +
        24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by
  classical
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let U := I0 ∪ I1
  let beta := ndA5BandBeta B branch
  let tau := ndA5BandTailThreshold B branch
  let Z0 := ndA5TubeRawMass A W
  let base : ℕ → ℝ := fun nu =>
    ndA5RawQ A W nu *
      ndA5OpenLatticeCount beta
        (Int.fract (A + (nu : ℝ) * logTwoThree))
  let corr : ℕ → ℝ := fun nu =>
    (ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu) *
      (if tau < Int.fract (A + (nu : ℝ) * logTwoThree)
       then (1 : ℝ) else 0)
  have hcount : 0 < ndA5BandCount B branch := by
    have := ndA5BandCount_ge_three_of_guards
      (branch := branch) hB hlogB
    omega
  have hbetaRange := ndA5BandBeta_mem_Ico hcount
  have hbeta : beta ∈ Set.Icc (0 : ℝ) 2 := by
    dsimp [beta]
    exact ⟨by linarith [hbetaRange.1], hbetaRange.2.le⟩
  have hbase0 :=
    abs_sum_ndA5RawQ_mul_openLattice_sub_mass_mul_mean_le_of_analytic
      hPhase hTube0 (A : UnitAddCircle) beta hbeta
  have hbase :
      |(∑ nu ∈ I0, base nu) - Z0 * (beta / Real.log 2)| ≤
        Z0 *
          (ndEndpointDbar c kappa I0.card *
            (64 * (I0.card : ℝ) * W /
              (ndA5TubeLo A W : ℝ))) := by
    simpa only [W, I0, beta, Z0, base,
      ndUnitRep_ndPhaseOrbit_real_eq_fract] using hbase0
  have hbaseUnion :
      (∑ nu ∈ U, base nu) = ∑ nu ∈ I0, base nu := by
    simpa [U, I0, I1, base] using
      sum_ndA5RawQ_mul_fullTube_union_eq A (A + 1) W
        (fun nu => ndA5OpenLatticeCount beta
          (Int.fract (A + (nu : ℝ) * logTwoThree)))
  have hdecomp :
      (∑ nu ∈ U,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandRawQTerm B branch A W nu r) =
        (∑ nu ∈ U, base nu) + ∑ nu ∈ U, corr nu := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro nu _hnu
    simpa [base, corr, beta, tau] using
      sum_ndA5NominalStrictBandRawQ_eq_baseOpen_add_shiftError
        (A := A) (W := W) (nu := nu) hB hlogB
  have hcorrPoint : ∀ nu ∈ U,
      |corr nu| ≤
        |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| := by
    intro nu _hnu
    dsimp [corr]
    by_cases htail : tau < Int.fract (A + (nu : ℝ) * logTwoThree)
    · simp [htail]
    · simp [htail]
  have hcorrAbs :
      |∑ nu ∈ U, corr nu| ≤
        ∑ nu ∈ U,
          |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| := by
    calc
      |∑ nu ∈ U, corr nu| ≤ ∑ nu ∈ U, |corr nu| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ nu ∈ U,
          |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| :=
        Finset.sum_le_sum hcorrPoint
  have hcorr :
      |∑ nu ∈ U, corr nu| ≤
        2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
          24 / Real.sqrt (Tao.taoSection5N0 B : ℝ) :=
    hcorrAbs.trans (by
      simpa [U, I0, I1, W, Z0] using
        sum_abs_ndA5RawQ_add_one_sub_le_of_analytic
          hlogB hTube0 hTube1)
  change |(∑ nu ∈ U,
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandRawQTerm B branch A W nu r) -
      Z0 * (beta / Real.log 2)| ≤
    Z0 *
        (ndEndpointDbar c kappa I0.card *
          (64 * (I0.card : ℝ) * W /
            (ndA5TubeLo A W : ℝ))) +
      (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
        24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))
  rw [hdecomp, hbaseUnion]
  calc
    |(∑ nu ∈ I0, base nu) + (∑ nu ∈ U, corr nu) -
        Z0 * (beta / Real.log 2)| =
        |((∑ nu ∈ I0, base nu) - Z0 * (beta / Real.log 2)) +
          ∑ nu ∈ U, corr nu| := by ring
    _ ≤ |(∑ nu ∈ I0, base nu) - Z0 * (beta / Real.log 2)| +
          |∑ nu ∈ U, corr nu| := abs_add_le _ _
    _ ≤ Z0 *
          (ndEndpointDbar c kappa I0.card *
            (64 * (I0.card : ℝ) * W /
              (ndA5TubeLo A W : ℝ))) +
        (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
          24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) :=
      add_le_add hbase hcorr

end

end ND
end Erdos1135
