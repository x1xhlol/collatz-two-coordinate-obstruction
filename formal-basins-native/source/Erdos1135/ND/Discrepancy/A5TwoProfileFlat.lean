import Erdos1135.ND.Discrepancy.A5TwoProfileReciprocal

/-!
# A5 Actual-Band Flat Two-Profile Consumer

This leaf attaches the frozen exponential cell weights to the actual strict
two-cell raw census.  The base flat profile is corrected by the same raw
neighbor difference used by the reciprocal endpoint, now multiplied by a
strictly gated upper-cell weight bounded by `exp beta`.
-/

open scoped BigOperators
open AddCircle

namespace Erdos1135
namespace ND

noncomputable section

/-- The strictly gated exponential weight of the actual upper flat cell. -/
noncomputable def ndA5ActualBandUpperFlatWeight
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (t : ℝ) : ℝ :=
  if ndA5BandTailThreshold B branch < t
  then Real.exp ((2 - t) * Real.log 2) else 0

theorem ndA5ActualBandUpperFlatWeight_nonneg
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (t : ℝ) :
    0 ≤ ndA5ActualBandUpperFlatWeight B branch t := by
  unfold ndA5ActualBandUpperFlatWeight
  split_ifs <;> positivity

/-- Activity of the upper cell places its exponential weight strictly below
the band endpoint `exp beta`; inactivity gives zero. -/
theorem ndA5ActualBandUpperFlatWeight_lt_exp_beta
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {t : ℝ} :
    ndA5ActualBandUpperFlatWeight B branch t <
      Real.exp (ndA5BandBeta B branch) := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  unfold ndA5ActualBandUpperFlatWeight
  by_cases htail : ndA5BandTailThreshold B branch < t
  · rw [if_pos htail]
    apply Real.exp_lt_exp.mpr
    have hposition :
        2 - t < ndA5BandBeta B branch / Real.log 2 := by
      unfold ndA5BandTailThreshold at htail
      linarith
    exact (lt_div_iff₀ hlogTwoPos).mp hposition
  · rw [if_neg htail]
    exact Real.exp_pos _

/-- The actual band endpoint exponential is strictly below four. -/
theorem exp_ndA5BandBeta_lt_four
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    Real.exp (ndA5BandBeta B branch) < 4 := by
  calc
    Real.exp (ndA5BandBeta B branch) <
        Real.exp (2 * Real.log 2) :=
      Real.exp_lt_exp.mpr
        (ndA5BandBeta_lt_two_mul_logTwo
          (branch := branch) hB hlogB)
    _ = 4 := by
      rw [two_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- For the actual quotient width, the flat profile consists of the always
active base cell and the strictly gated upper cell. -/
theorem ndA5FlatPhaseProfile_actualBand_eq_base_add_upper
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {t : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ndA5FlatPhaseProfile (ndA5BandBeta B branch) t =
      Real.exp ((1 - t) * Real.log 2) +
        ndA5ActualBandUpperFlatWeight B branch t := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hp (K : ℝ) (hK : 1 ≤ K) :
      (0 < (K - t) * Real.log 2 ∧
          (K - t) * Real.log 2 < ndA5BandBeta B branch) ↔
        K - ndA5BandBeta B branch / Real.log 2 < t := by
    have hKt : 0 < K - t := sub_pos.mpr (ht.2.trans_le hK)
    constructor
    · rintro ⟨_hlower, hupper⟩
      have hdiv : K - t < ndA5BandBeta B branch / Real.log 2 :=
        (lt_div_iff₀ hlogTwoPos).2 hupper
      linarith
    · intro hthreshold
      constructor
      · exact mul_pos hKt hlogTwoPos
      · apply (lt_div_iff₀ hlogTwoPos).1
        linarith
  have hthreshold := ndA5BandTailThreshold_mem_Ioo
    (branch := branch) hB hlogB
  have hfirst :
      1 - ndA5BandBeta B branch / Real.log 2 < t := by
    unfold ndA5BandTailThreshold at hthreshold
    linarith [hthreshold.2, ht.1]
  have hthird :
      ¬(3 - ndA5BandBeta B branch / Real.log 2 < t) := by
    unfold ndA5BandTailThreshold at hthreshold
    linarith [hthreshold.1, ht.2]
  simp only [ndA5FlatPhaseProfile, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, zero_add]
  simp only [hp 1 (by norm_num), hp 2 (by norm_num),
    hp 3 (by norm_num)]
  rw [if_pos hfirst, if_neg hthird]
  simp [ndA5ActualBandUpperFlatWeight, ndA5BandTailThreshold]

/-- The literal weighted two-cell sum is the base flat profile plus the raw
neighbor difference times the gated upper-cell weight. -/
theorem sum_ndA5NominalStrictBandFlatRawQ_eq_baseFlat_add_shiftError
    {B nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {A W : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    (∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandFlatRawQTerm B branch A W nu r) =
      ndA5RawQ A W nu *
          ndA5FlatPhaseProfile (ndA5BandBeta B branch)
            (Int.fract (A + (nu : ℝ) * logTwoThree)) +
        (ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu) *
          ndA5ActualBandUpperFlatWeight B branch
            (Int.fract (A + (nu : ℝ) * logTwoThree)) := by
  let t := Int.fract (A + (nu : ℝ) * logTwoThree)
  have ht : t ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hbase :
      ndA5NominalStrictBandLevel (ndA5BandBeta B branch) A nu
        (ndA5PhysicalLevelInt A nu) :=
    (ndA5NominalStrictBandLevel_iff_base_or_firstShift hB hlogB).2
      (Or.inl rfl)
  have hshift :
      ndA5NominalStrictBandLevel (ndA5BandBeta B branch) A nu
          (ndA5PhysicalLevelInt (A + 1) nu) ↔
        ndA5BandTailThreshold B branch < t := by
    constructor
    · intro h
      rcases
          (ndA5NominalStrictBandLevel_iff_base_or_firstShift
            hB hlogB).1 h with hsame | ⟨hnext, hphase⟩
      · have htranslate := ndA5PhysicalLevelInt_add_nat A nu 1
        norm_num at htranslate
        rw [htranslate] at hsame
        omega
      · simpa [t] using hphase
    · intro hphase
      apply (ndA5NominalStrictBandLevel_iff_base_or_firstShift
        hB hlogB).2
      right
      exact ⟨by simpa using ndA5PhysicalLevelInt_add_nat A nu 1,
        by simpa [t] using hphase⟩
  have hprofile :=
    ndA5FlatPhaseProfile_actualBand_eq_base_add_upper
      (branch := branch) hB hlogB ht
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [ndA5NominalStrictBandFlatRawQTerm]
  simp [ndA5NominalStrictBandRawQTerm, hbase, hshift]
  dsimp [t] at hprofile ⊢
  rw [hprofile]
  by_cases htail : ndA5BandTailThreshold B branch <
      Int.fract (A + (nu : ℝ) * logTwoThree)
  · simp [ndA5ActualBandUpperFlatWeight, htail]
    ring
  · simp [ndA5ActualBandUpperFlatWeight, htail]

/-- The checked normalized flat endpoint lifted to the raw base carrier. -/
theorem abs_sum_ndA5RawQ_mul_flat_sub_mass_mul_mean_le_of_analytic
    {B : ℕ} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hTube : NDA5AnalyticTubeFacts B C A)
    (phi : UnitAddCircle) (beta : ℝ)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 2) :
    |(∑ nu ∈ ndA5FullTube A (ndA5TubeWidth B C),
        ndA5RawQ A (ndA5TubeWidth B C) nu *
          ndA5FlatPhaseProfile beta
            (ndUnitRep (ndPhaseOrbit phi nu))) -
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        ndA5FlatPhaseMean beta| ≤
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        ((2 * Real.exp beta - 1) *
          ndEndpointDbar c kappa
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
    (F := fun nu => ndA5FlatPhaseProfile beta
      (ndUnitRep (ndPhaseOrbit phi nu)))
    (mu := ndA5FlatPhaseMean beta)
    (E := (2 * Real.exp beta - 1) *
      ndEndpointDbar c kappa
        (ndA5FullTube A (ndA5TubeWidth B C)).card *
      (64 *
        ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
        ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ))) hZ
  exact abs_sum_ndA5NormalizedQ_mul_flat_sub_mean_le_of_analytic
    hPhase hTube phi beta hbeta

/-- Terminal raw flat endpoint for the actual weighted two-cell band.  The
base flat discrepancy is rescaled by `Z_A`; the raw first-shift L1 error is
multiplied only by the sharp gated-cell ceiling `exp beta`. -/
theorem abs_sum_ndA5NominalStrictBandFlatRawQ_sub_mass_mul_mean_le_of_analytic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    {c kappa : ℝ} (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube0 : NDA5AnalyticTubeFacts B C A)
    (hTube1 : NDA5AnalyticTubeFacts B C (A + 1)) :
    |(∑ nu ∈
        ndA5FullTube A (ndA5TubeWidth B C) ∪
          ndA5FullTube (A + 1) (ndA5TubeWidth B C),
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch A
            (ndA5TubeWidth B C) nu r) -
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        ndA5FlatPhaseMean (ndA5BandBeta B branch)| ≤
      ndA5TubeRawMass A (ndA5TubeWidth B C) *
        ((2 * Real.exp (ndA5BandBeta B branch) - 1) *
          ndEndpointDbar c kappa
            (ndA5FullTube A (ndA5TubeWidth B C)).card *
          (64 *
            ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
            ndA5TubeWidth B C /
              (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ))) +
        Real.exp (ndA5BandBeta B branch) *
          (2 * (ndA5TubeWidth B C /
              (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ)) *
            ndA5TubeRawMass A (ndA5TubeWidth B C) +
          24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by
  classical
  let W := ndA5TubeWidth B C
  let I0 := ndA5FullTube A W
  let I1 := ndA5FullTube (A + 1) W
  let Ucarrier := I0 ∪ I1
  let beta := ndA5BandBeta B branch
  let Z0 := ndA5TubeRawMass A W
  let base : ℕ → ℝ := fun nu =>
    ndA5RawQ A W nu *
      ndA5FlatPhaseProfile beta
        (Int.fract (A + (nu : ℝ) * logTwoThree))
  let corr : ℕ → ℝ := fun nu =>
    (ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu) *
      ndA5ActualBandUpperFlatWeight B branch
        (Int.fract (A + (nu : ℝ) * logTwoThree))
  have hcount : 0 < ndA5BandCount B branch := by
    have := ndA5BandCount_ge_three_of_guards
      (branch := branch) hB hlogB
    omega
  have hbetaRange := ndA5BandBeta_mem_Ico hcount
  have hbeta : beta ∈ Set.Icc (0 : ℝ) 2 := by
    dsimp [beta]
    exact ⟨by linarith [hbetaRange.1], hbetaRange.2.le⟩
  have hbase0 :=
    abs_sum_ndA5RawQ_mul_flat_sub_mass_mul_mean_le_of_analytic
      hPhase hTube0 (A : UnitAddCircle) beta hbeta
  have hbase :
      |(∑ nu ∈ I0, base nu) -
          Z0 * ndA5FlatPhaseMean beta| ≤
        Z0 *
          ((2 * Real.exp beta - 1) *
            ndEndpointDbar c kappa I0.card *
            (64 * (I0.card : ℝ) * W /
              (ndA5TubeLo A W : ℝ))) := by
    simpa only [W, I0, beta, Z0, base,
      ndUnitRep_ndPhaseOrbit_real_eq_fract] using hbase0
  have hbaseUnion :
      (∑ nu ∈ Ucarrier, base nu) = ∑ nu ∈ I0, base nu := by
    simpa [Ucarrier, I0, I1, base] using
      sum_ndA5RawQ_mul_fullTube_union_eq A (A + 1) W
        (fun nu => ndA5FlatPhaseProfile beta
          (Int.fract (A + (nu : ℝ) * logTwoThree)))
  have hdecomp :
      (∑ nu ∈ Ucarrier,
        ∑ r ∈ Finset.range 2,
          ndA5NominalStrictBandFlatRawQTerm B branch A W nu r) =
        (∑ nu ∈ Ucarrier, base nu) +
          ∑ nu ∈ Ucarrier, corr nu := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro nu _hnu
    simpa [base, corr, beta] using
      sum_ndA5NominalStrictBandFlatRawQ_eq_baseFlat_add_shiftError
        (A := A) (W := W) (nu := nu) hB hlogB
  have hcorrPoint : ∀ nu ∈ Ucarrier,
      |corr nu| ≤ Real.exp beta *
        |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| := by
    intro nu _hnu
    let t := Int.fract (A + (nu : ℝ) * logTwoThree)
    have hUnonneg :
        0 ≤ ndA5ActualBandUpperFlatWeight B branch t :=
      ndA5ActualBandUpperFlatWeight_nonneg B branch t
    have hUle :
        ndA5ActualBandUpperFlatWeight B branch t ≤ Real.exp beta := by
      exact (by
        dsimp [beta]
        exact le_of_lt ndA5ActualBandUpperFlatWeight_lt_exp_beta)
    dsimp [corr, t] at hUnonneg hUle ⊢
    rw [abs_mul, abs_of_nonneg hUnonneg]
    calc
      |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| *
          ndA5ActualBandUpperFlatWeight B branch
            (Int.fract (A + (nu : ℝ) * logTwoThree)) ≤
          |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| *
            Real.exp beta :=
        mul_le_mul_of_nonneg_left hUle (abs_nonneg _)
      _ = Real.exp beta *
          |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| := by ring
  have hcorrAbs :
      |∑ nu ∈ Ucarrier, corr nu| ≤
        Real.exp beta *
          ∑ nu ∈ Ucarrier,
            |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| := by
    calc
      |∑ nu ∈ Ucarrier, corr nu| ≤
          ∑ nu ∈ Ucarrier, |corr nu| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ nu ∈ Ucarrier,
          Real.exp beta *
            |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| :=
        Finset.sum_le_sum hcorrPoint
      _ = Real.exp beta *
          ∑ nu ∈ Ucarrier,
            |ndA5RawQ (A + 1) W nu - ndA5RawQ A W nu| := by
        rw [Finset.mul_sum]
  have hcorr :
      |∑ nu ∈ Ucarrier, corr nu| ≤
        Real.exp beta *
          (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
            24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) := by
    apply hcorrAbs.trans
    apply mul_le_mul_of_nonneg_left
    · simpa [Ucarrier, I0, I1, W, Z0] using
        sum_abs_ndA5RawQ_add_one_sub_le_of_analytic
          hlogB hTube0 hTube1
    · exact (Real.exp_pos beta).le
  change |(∑ nu ∈ Ucarrier,
      ∑ r ∈ Finset.range 2,
        ndA5NominalStrictBandFlatRawQTerm B branch A W nu r) -
      Z0 * ndA5FlatPhaseMean beta| ≤
    Z0 *
        ((2 * Real.exp beta - 1) *
          ndEndpointDbar c kappa I0.card *
          (64 * (I0.card : ℝ) * W /
            (ndA5TubeLo A W : ℝ))) +
      Real.exp beta *
        (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
          24 / Real.sqrt (Tao.taoSection5N0 B : ℝ))
  rw [hdecomp, hbaseUnion]
  calc
    |(∑ nu ∈ I0, base nu) + (∑ nu ∈ Ucarrier, corr nu) -
        Z0 * ndA5FlatPhaseMean beta| =
        |((∑ nu ∈ I0, base nu) -
            Z0 * ndA5FlatPhaseMean beta) +
          ∑ nu ∈ Ucarrier, corr nu| := by ring
    _ ≤ |(∑ nu ∈ I0, base nu) -
            Z0 * ndA5FlatPhaseMean beta| +
          |∑ nu ∈ Ucarrier, corr nu| := abs_add_le _ _
    _ ≤ Z0 *
          ((2 * Real.exp beta - 1) *
            ndEndpointDbar c kappa I0.card *
            (64 * (I0.card : ℝ) * W /
              (ndA5TubeLo A W : ℝ))) +
        Real.exp beta *
          (2 * (W / (ndA5TubeLo A W : ℝ)) * Z0 +
            24 / Real.sqrt (Tao.taoSection5N0 B : ℝ)) :=
      add_le_add hbase hcorr

end

end ND
end Erdos1135
