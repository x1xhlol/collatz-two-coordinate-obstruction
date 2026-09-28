import Erdos1135.ND.Band.A5RawMass
import Erdos1135.ND.Band.A5StrictBandLevels

/-!
# A5 Actual-Band Two-Profile Raw Assembler

The actual Part-A quotient width admits only the strict anchor and its first
successor.  This leaf turns that signed enumeration into the corresponding
two-term raw `q` profile.  The two summands keep their own phases and hence
their own eventual normalizing masses; no carrier equality or common-mass
replacement is made here.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- The raw `q` contribution of one nominal dyadic offset.  The classical
decision is confined to this noncomputable finite profile. -/
noncomputable def ndA5NominalStrictBandRawQTerm
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (A W : ℝ) (nu r : ℕ) : ℝ :=
  @ite ℝ
    (ndA5NominalStrictBandLevel (ndA5BandBeta B branch) A nu
      (ndA5PhysicalLevelInt (A + (r : ℝ)) nu))
    (Classical.propDecidable _)
    (ndA5RawQ (A + (r : ℝ)) W nu) 0

/-- The literal exponentially weighted nominal raw term. Its strict nominal
indicator is inherited from `ndA5NominalStrictBandRawQTerm`; the exponential
factor is attached exactly once here. -/
noncomputable def ndA5NominalStrictBandFlatRawQTerm
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (A W : ℝ) (nu r : ℕ) : ℝ :=
  ndA5NominalStrictBandRawQTerm B branch A W nu r *
    Real.exp (((((r + 1 : ℕ) : ℝ) -
      Int.fract (A + (nu : ℝ) * logTwoThree))) * Real.log 2)

/-- The literal two-cell nominal raw sum is the base raw profile plus the
strictly thresholded first-shift profile.

This is a pointwise identity at the original index `nu`.  In particular, the
shifted term is `ndA5RawQ (A + 1) W nu`; it does not change the outer endpoint
or replace its raw mass by the base mass. -/
theorem sum_ndA5NominalStrictBandRawQ_eq_base_add_firstShift
    {B nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {A W : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    (∑ r ∈ Finset.range 2,
      ndA5NominalStrictBandRawQTerm B branch A W nu r) =
      ndA5RawQ A W nu +
        if ndA5BandTailThreshold B branch <
            Int.fract (A + (nu : ℝ) * logTwoThree)
        then ndA5RawQ (A + 1) W nu else 0 := by
  classical
  have hbase :
      ndA5NominalStrictBandLevel (ndA5BandBeta B branch) A nu
        (ndA5PhysicalLevelInt A nu) :=
    (ndA5NominalStrictBandLevel_iff_base_or_firstShift hB hlogB).2
      (Or.inl rfl)
  have hshift :
      ndA5NominalStrictBandLevel (ndA5BandBeta B branch) A nu
          (ndA5PhysicalLevelInt (A + 1) nu) ↔
        ndA5BandTailThreshold B branch <
          Int.fract (A + (nu : ℝ) * logTwoThree) := by
    constructor
    · intro h
      rcases
          (ndA5NominalStrictBandLevel_iff_base_or_firstShift
            hB hlogB).1 h with hsame | ⟨hnext, hphase⟩
      · have htranslate := ndA5PhysicalLevelInt_add_nat A nu 1
        norm_num at htranslate
        rw [htranslate] at hsame
        omega
      · exact hphase
    · intro hphase
      apply (ndA5NominalStrictBandLevel_iff_base_or_firstShift
        hB hlogB).2
      right
      exact ⟨by simpa using ndA5PhysicalLevelInt_add_nat A nu 1, hphase⟩
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp [ndA5NominalStrictBandRawQTerm, hbase, hshift]

end

end ND
end Erdos1135
