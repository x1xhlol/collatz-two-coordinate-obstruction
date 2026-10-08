import Erdos1135.ND.Band.A5Physical

/-!
# A5 Strict Nominal Band Levels

This leaf freezes the finite-level arithmetic used after the once-only
exact-affine/strip-boundary charge in frozen v10.  The anchor is the strict
integer lift `floor Lo + 1`, including at integral phase.  At the actual
Part-A band width, the nominal fiber consists of the anchor and, above one
explicit phase threshold, its first successor.

The statements remain signed.  They do not pass through `Int.toNat`, and they
do not identify nominal membership with the exact affine preimage before the
separate boundary charge.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Nominal post-boundary membership of a signed level in one strict A5 band.
Both endpoints are strict, as in the frozen source's positions
`u_r = (r + 1 - fract Lo) * log 2` in `(0, beta)`. -/
def ndA5NominalStrictBandLevel
    (beta A : ℝ) (nu : ℕ) (L : ℤ) : Prop :=
  0 < ((L : ℝ) - (A + (nu : ℝ) * logTwoThree)) * Real.log 2 ∧
    ((L : ℝ) - (A + (nu : ℝ) * logTwoThree)) * Real.log 2 < beta

/-- Fractional-phase threshold above which the first shifted level is active. -/
noncomputable def ndA5BandTailThreshold
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : ℝ :=
  2 - ndA5BandBeta B branch / Real.log 2

/-- The source scale guard gives at least three equal logarithmic bands.
The actual bound is much larger; three is the minimal input needed below. -/
theorem ndA5BandCount_ge_three_of_guards
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    3 ≤ ndA5BandCount B branch := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogSource :
      Real.log (Tao.taoSection5SourceY B branch) =
        Tao.taoSection5BranchExponent branch * Real.log B := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.log_rpow hBpos _
  have hwidth : (300 : ℝ) ≤ ndA5BandLogWidth B branch := by
    unfold ndA5BandLogWidth
    rw [hlogSource]
    cases branch <;>
      norm_num [alpha, Tao.taoAlpha, Tao.taoSection5BranchExponent] at * <;>
      nlinarith
  unfold ndA5BandCount
  apply Nat.le_floor
  exact (by norm_num : (3 : ℝ) ≤ 300).trans hwidth

/-- At the actual frozen Part-A scale, the quotient band width is strictly
smaller than two dyadic lattice spacings. -/
theorem ndA5BandBeta_lt_two_mul_logTwo
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    ndA5BandBeta B branch < 2 * Real.log 2 := by
  have hcount : 3 ≤ ndA5BandCount B branch :=
    ndA5BandCount_ge_three_of_guards hB hlogB
  have hcountPos : 0 < ndA5BandCount B branch := by omega
  have hcountRealPos : (0 : ℝ) < ndA5BandCount B branch := by
    exact_mod_cast hcountPos
  have hcountRealThree : (3 : ℝ) ≤ ndA5BandCount B branch := by
    exact_mod_cast hcount
  have hwidthLt :
      ndA5BandLogWidth B branch <
        (ndA5BandCount B branch : ℝ) + 1 := by
    simpa [ndA5BandCount] using
      Nat.lt_floor_add_one (ndA5BandLogWidth B branch)
  have hlogTwoLower : (69 / 100 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hfourThirds : (4 / 3 : ℝ) < 2 * Real.log 2 := by
    linarith
  unfold ndA5BandBeta
  apply (div_lt_iff₀ hcountRealPos).2
  calc
    ndA5BandLogWidth B branch <
        (ndA5BandCount B branch : ℝ) + 1 := hwidthLt
    _ ≤ (4 / 3 : ℝ) * (ndA5BandCount B branch : ℝ) := by
      nlinarith
    _ < (2 * Real.log 2) * (ndA5BandCount B branch : ℝ) :=
      mul_lt_mul_of_pos_right hfourThirds hcountRealPos

/-- The first-shift phase threshold is strictly between zero and one. -/
theorem ndA5BandTailThreshold_mem_Ioo
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    ndA5BandTailThreshold B branch ∈ Set.Ioo (0 : ℝ) 1 := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogTwoLtOne : Real.log (2 : ℝ) < 1 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hcount : 0 < ndA5BandCount B branch := by
    have := ndA5BandCount_ge_three_of_guards
      (branch := branch) hB hlogB
    omega
  have hbetaRange := ndA5BandBeta_mem_Ico hcount
  have hbetaUpper := ndA5BandBeta_lt_two_mul_logTwo
    (branch := branch) hB hlogB
  have hlogTwoLtBeta : Real.log 2 < ndA5BandBeta B branch :=
    hlogTwoLtOne.trans_le hbetaRange.1
  have hratioUpper :
      ndA5BandBeta B branch / Real.log 2 < 2 := by
    exact (div_lt_iff₀ hlogTwoPos).2 (by simpa [two_mul] using hbetaUpper)
  have hratioLower :
      1 < ndA5BandBeta B branch / Real.log 2 := by
    exact (lt_div_iff₀ hlogTwoPos).2 (by simpa using hlogTwoLtBeta)
  unfold ndA5BandTailThreshold
  constructor <;> linarith

/-- Any active signed nominal level is the strict anchor or its successor.
This support lemma intentionally precedes the exact phase-threshold identity. -/
theorem ndA5StrictBandLevel_eq_base_or_add_one_of_guards
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    {Lo : ℝ} {L : ℤ}
    (hL : 0 < ((L : ℝ) - Lo) * Real.log 2 ∧
      ((L : ℝ) - Lo) * Real.log 2 < ndA5BandBeta B branch) :
    L = Int.floor Lo + 1 ∨ L = (Int.floor Lo + 1) + 1 := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hbetaUpper := ndA5BandBeta_lt_two_mul_logTwo
    (branch := branch) hB hlogB
  have hLoL : Lo < (L : ℝ) := by
    have := (pos_of_mul_pos_left hL.1 hlogTwoPos.le)
    linarith
  have hfloorLe := Int.floor_le Lo
  push_cast at hfloorLe
  have hfloorLtLReal : (Int.floor Lo : ℝ) < (L : ℝ) :=
    hfloorLe.trans_lt hLoL
  have hfloorLtL : Int.floor Lo < L := by
    exact_mod_cast hfloorLtLReal
  have hdiffLt : (L : ℝ) - Lo < 2 := by
    exact lt_of_mul_lt_mul_right (hL.2.trans hbetaUpper) hlogTwoPos.le
  have hLoLtFloor := Int.lt_floor_add_one Lo
  push_cast at hLoLtFloor
  have hLlt3Real : (L : ℝ) < (Int.floor Lo : ℝ) + 3 := by
    linarith
  have hLlt3 : L < Int.floor Lo + 3 := by
    exact_mod_cast hLlt3Real
  omega

/-- Translating the real phase by a natural number translates the signed
strict level by the same integer.  This is the adapter from the nominal
successor above to the independently checked `A + r` analytic packets. -/
theorem ndA5PhysicalLevelInt_add_nat
    (A : ℝ) (nu r : ℕ) :
    ndA5PhysicalLevelInt (A + (r : ℝ)) nu =
      ndA5PhysicalLevelInt A nu + (r : ℤ) := by
  unfold ndA5PhysicalLevelInt
  rw [show A + (r : ℝ) + (nu : ℝ) * logTwoThree =
      (A + (nu : ℝ) * logTwoThree) + (r : ℝ) by ring,
    Int.floor_add_natCast]
  omega

private theorem ndA5PhysicalLevelInt_position_eq_one_sub_fract
    (A : ℝ) (nu : ℕ) :
    (ndA5PhysicalLevelInt A nu : ℝ) -
        (A + (nu : ℝ) * logTwoThree) =
      1 - Int.fract (A + (nu : ℝ) * logTwoThree) := by
  unfold ndA5PhysicalLevelInt Int.fract
  push_cast
  ring

private theorem ndA5PhysicalLevelInt_add_one_position_eq_two_sub_fract
    (A : ℝ) (nu : ℕ) :
    ((ndA5PhysicalLevelInt A nu + 1 : ℤ) : ℝ) -
        (A + (nu : ℝ) * logTwoThree) =
      2 - Int.fract (A + (nu : ℝ) * logTwoThree) := by
  unfold ndA5PhysicalLevelInt Int.fract
  push_cast
  ring

/-- Exact strict two-cell decomposition for the actual A5 band.

The base strict anchor is always active.  Its successor is active exactly
when the fractional phase is strictly above `2 - beta / log 2`; equality is
excluded.  This is the nominal theorem after the source's once-only
exact-affine boundary charge, not an identification with the uncharged
physical preimage. -/
theorem ndA5NominalStrictBandLevel_iff_base_or_firstShift
    {B nu : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {A : ℝ} {L : ℤ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) :
    ndA5NominalStrictBandLevel (ndA5BandBeta B branch) A nu L ↔
      L = ndA5PhysicalLevelInt A nu ∨
        (L = ndA5PhysicalLevelInt A nu + 1 ∧
          ndA5BandTailThreshold B branch <
            Int.fract (A + (nu : ℝ) * logTwoThree)) := by
  let Lo : ℝ := A + (nu : ℝ) * logTwoThree
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogTwoLtOne : Real.log (2 : ℝ) < 1 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hcount : 0 < ndA5BandCount B branch := by
    have := ndA5BandCount_ge_three_of_guards
      (branch := branch) hB hlogB
    omega
  have hbetaRange := ndA5BandBeta_mem_Ico hcount
  constructor
  · intro hlevel
    have hlevel' :
        0 < ((L : ℝ) - Lo) * Real.log 2 ∧
          ((L : ℝ) - Lo) * Real.log 2 < ndA5BandBeta B branch := by
      simpa [ndA5NominalStrictBandLevel, Lo] using hlevel
    rcases ndA5StrictBandLevel_eq_base_or_add_one_of_guards
        hB hlogB hlevel' with hbase | hshift
    · left
      simpa [ndA5PhysicalLevelInt, Lo] using hbase
    · right
      have hshift' : L = ndA5PhysicalLevelInt A nu + 1 := by
        simpa [ndA5PhysicalLevelInt, Lo] using hshift
      refine ⟨hshift', ?_⟩
      have hupper := hlevel'.2
      rw [hshift'] at hupper
      rw [ndA5PhysicalLevelInt_add_one_position_eq_two_sub_fract] at hupper
      have hdiv :
          2 - Int.fract (A + (nu : ℝ) * logTwoThree) <
            ndA5BandBeta B branch / Real.log 2 :=
        (lt_div_iff₀ hlogTwoPos).2 hupper
      unfold ndA5BandTailThreshold
      linarith
  · intro hlevel
    rcases hlevel with hbase | ⟨hshift, hphase⟩
    · subst L
      unfold ndA5NominalStrictBandLevel
      rw [ndA5PhysicalLevelInt_position_eq_one_sub_fract]
      constructor
      · exact mul_pos (sub_pos.mpr (Int.fract_lt_one _)) hlogTwoPos
      · have hcoefLe :
            1 - Int.fract (A + (nu : ℝ) * logTwoThree) ≤ 1 := by
          linarith [Int.fract_nonneg (A + (nu : ℝ) * logTwoThree)]
        have hmulLe :
            (1 - Int.fract (A + (nu : ℝ) * logTwoThree)) * Real.log 2 ≤
              Real.log 2 := by
          simpa using mul_le_mul_of_nonneg_right hcoefLe hlogTwoPos.le
        linarith [hbetaRange.1]
    · subst L
      unfold ndA5NominalStrictBandLevel
      rw [ndA5PhysicalLevelInt_add_one_position_eq_two_sub_fract]
      constructor
      · have hfract := Int.fract_lt_one
            (A + (nu : ℝ) * logTwoThree)
        exact mul_pos (by linarith) hlogTwoPos
      · have hdiv :
            2 - Int.fract (A + (nu : ℝ) * logTwoThree) <
              ndA5BandBeta B branch / Real.log 2 := by
          unfold ndA5BandTailThreshold at hphase
          linarith
        exact (lt_div_iff₀ hlogTwoPos).1 hdiv

end

end ND
end Erdos1135
