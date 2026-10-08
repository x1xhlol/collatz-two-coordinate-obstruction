import Erdos1135.ND.Band.A5StrictBandLevels
import Erdos1135.ND.Discrepancy.A5PaddedProfile

/-!
# A5 Actual-Band First-Shift Tail

This leaf specializes the checked coefficient-one open-lattice endpoint to
the single conditional `A + 1` cell of the actual Part-A band.  Only the
shifted normalized profile is used here.  Its own raw mass is restored by a
later consumer before it is combined with the distinct base profile.
-/

open scoped BigOperators
open AddCircle

namespace Erdos1135
namespace ND

noncomputable section

/-- The chosen representative of the real-anchored phase orbit is the
ordinary fractional part of the affine phase. -/
theorem ndUnitRep_ndPhaseOrbit_real_eq_fract
    (A : ℝ) (nu : ℕ) :
    ndUnitRep (ndPhaseOrbit (A : UnitAddCircle) nu) =
      Int.fract (A + (nu : ℝ) * logTwoThree) := by
  let x : ℝ := A + (nu : ℝ) * logTwoThree
  have horbit :
      ndPhaseOrbit (A : UnitAddCircle) nu = (x : UnitAddCircle) := by
    dsimp [x]
    unfold ndPhaseOrbit
    rw [← AddCircle.coe_nsmul]
    rw [show (nu • logTwoThree : ℝ) =
        (nu : ℝ) * logTwoThree by simp [nsmul_eq_mul]]
  calc
    ndUnitRep (ndPhaseOrbit (A : UnitAddCircle) nu) =
        ndUnitRep (x : UnitAddCircle) := congrArg ndUnitRep horbit
    _ = ndUnitRep ((Int.fract x : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_fract]
    _ = Int.fract x := ndUnitRep_coe (Int.fract x)
      ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    _ = Int.fract (A + (nu : ℝ) * logTwoThree) := by rfl

/-- At the actual quotient width, the literal open-lattice count is one
unconditional base cell plus the strict first-shift tail. -/
theorem ndA5OpenLatticeCount_actualBand_eq_one_add_tail
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {t : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ndA5OpenLatticeCount (ndA5BandBeta B branch) t =
      1 + if ndA5BandTailThreshold B branch < t then 1 else 0 := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hp (K : ℝ) (hK : 1 ≤ K) :
      (0 < (K - t) * Real.log 2 ∧
          (K - t) * Real.log 2 < ndA5BandBeta B branch) ↔
        K - ndA5BandBeta B branch / Real.log 2 < t := by
    have hKt : 0 < K - t := sub_pos.mpr (ht.2.trans_le hK)
    constructor
    · rintro ⟨_hlower, hupper⟩
      have hdiv :
          K - t < ndA5BandBeta B branch / Real.log 2 :=
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
  simp only [ndA5OpenLatticeCount, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, zero_add]
  simp only [hp 1 (by norm_num), hp 2 (by norm_num),
    hp 3 (by norm_num)]
  rw [if_pos hfirst, if_neg hthird]
  simp [ndA5BandTailThreshold]

/-- Coefficient-one Abel control of the normalized conditional `A + 1`
profile.  The phase selector is still anchored at the original `A`, and the
mean is exactly `beta / log 2 - 1`. -/
theorem abs_sum_ndA5NormalizedQ_add_one_mul_bandTail_sub_mean_le_of_analytic
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {C A : ℝ}
    {c kappa : ℝ}
    (hPhase : PhaseGap c kappa)
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hTube1 : NDA5AnalyticTubeFacts B C (A + 1)) :
    |(∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
        ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
          (if ndA5BandTailThreshold B branch <
              Int.fract (A + (nu : ℝ) * logTwoThree)
           then (1 : ℝ) else 0)) -
      (ndA5BandBeta B branch / Real.log 2 - 1)| ≤
      ndEndpointDbar c kappa
          (ndA5FullTube (A + 1) (ndA5TubeWidth B C)).card *
        (64 *
          ((ndA5FullTube (A + 1) (ndA5TubeWidth B C)).card : ℝ) *
          ndA5TubeWidth B C /
            (ndA5TubeLo (A + 1) (ndA5TubeWidth B C) : ℝ)) := by
  have hcount : 0 < ndA5BandCount B branch := by
    have := ndA5BandCount_ge_three_of_guards
      (branch := branch) hB hlogB
    omega
  have hbetaRange := ndA5BandBeta_mem_Ico hcount
  have hbeta : ndA5BandBeta B branch ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨by linarith [hbetaRange.1], hbetaRange.2.le⟩
  have hopen :=
    abs_sum_ndA5NormalizedQ_mul_openLattice_sub_mean_le_of_analytic
      hPhase hTube1 (A : UnitAddCircle) (ndA5BandBeta B branch) hbeta
  have hsum := sum_ndA5NormalizedQ_eq_one_of_analytic hTube1
  have hsumOpen :
      (∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
        ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
          ndA5OpenLatticeCount (ndA5BandBeta B branch)
            (ndUnitRep (ndPhaseOrbit (A : UnitAddCircle) nu))) =
        1 +
          ∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
            ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
              (if ndA5BandTailThreshold B branch <
                  Int.fract (A + (nu : ℝ) * logTwoThree)
               then (1 : ℝ) else 0) := by
    calc
      _ = ∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
            ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
              (1 + if ndA5BandTailThreshold B branch <
                  Int.fract (A + (nu : ℝ) * logTwoThree)
                then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        rw [ndA5OpenLatticeCount_actualBand_eq_one_add_tail
          (branch := branch) hB hlogB (ndUnitRep_mem_Ico _),
          ndUnitRep_ndPhaseOrbit_real_eq_fract]
      _ = ∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
            (ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu +
              ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
                (if ndA5BandTailThreshold B branch <
                    Int.fract (A + (nu : ℝ) * logTwoThree)
                 then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        ring
      _ =
          (∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
            ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu) +
          ∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
            ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
              (if ndA5BandTailThreshold B branch <
                  Int.fract (A + (nu : ℝ) * logTwoThree)
               then (1 : ℝ) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = 1 +
          ∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
            ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
              (if ndA5BandTailThreshold B branch <
                  Int.fract (A + (nu : ℝ) * logTwoThree)
               then (1 : ℝ) else 0) := by
        rw [hsum]
  have hcenter :
      ((∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
        ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
          ndA5OpenLatticeCount (ndA5BandBeta B branch)
            (ndUnitRep (ndPhaseOrbit (A : UnitAddCircle) nu))) -
          ndA5BandBeta B branch / Real.log 2) =
        ((∑ nu ∈ ndA5FullTube (A + 1) (ndA5TubeWidth B C),
          ndA5NormalizedQ (A + 1) (ndA5TubeWidth B C) nu *
            (if ndA5BandTailThreshold B branch <
                Int.fract (A + (nu : ℝ) * logTwoThree)
             then (1 : ℝ) else 0)) -
          (ndA5BandBeta B branch / Real.log 2 - 1)) := by
    rw [hsumOpen]
    ring
  rw [hcenter] at hopen
  exact hopen

end

end ND
end Erdos1135
