import Erdos1135.ND.Band.A5Physical
import Erdos1135.ND.Band.OddHalfOpenNormalizer

/-!
# A5 Half-Open Band Normalizers

This leaf specializes the checked half-open odd carrier to the consecutive
equal-log-width bands from frozen v10 Part A.  It keeps the adjacent lower
endpoints visible so that a later finite partition can telescope without
changing the upper-endpoint convention.

Positive band count already forces the source logarithmic width to be at
least one.  Together with `B >= 1`, this supplies enough scale for strict
ceiling separation and for the uniform `1 / 4` logarithmic-mass floor.  No
large eventual guard or valid-band-index hypothesis is needed here.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- Positive odd natural values in the `j`th exact A5 half-open band. -/
noncomputable def ndA5OddBand
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) : Finset ℕ :=
  oddHalfOpenRealWindow (ndA5BandLower B branch j)
    (ndA5BandLower B branch (j + 1))

/-- The zeroth A5 band starts at the source scale. -/
theorem ndA5BandLower_zero
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) :
    ndA5BandLower B branch 0 = Tao.taoSection5SourceY B branch := by
  simp [ndA5BandLower]

/-- Consecutive A5 lower endpoints differ by the common exponential ratio. -/
theorem ndA5BandLower_succ
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    ndA5BandLower B branch (j + 1) =
      ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) := by
  simp [ndA5BandLower, add_mul, Real.exp_add, mul_assoc]

/-- Additive width of one exact A5 band. -/
theorem ndA5BandLower_succ_sub
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    ndA5BandLower B branch (j + 1) - ndA5BandLower B branch j =
      ndA5BandLower B branch j *
        (Real.exp (ndA5BandBeta B branch) - 1) := by
  rw [ndA5BandLower_succ]
  ring

/-- Every A5 band endpoint lies above the base scale `B`. -/
theorem cast_le_ndA5BandLower
    {B : ℕ} (hB : 1 ≤ B)
    (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    (B : ℝ) ≤ ndA5BandLower B branch j := by
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsource :
      (B : ℝ) ≤ Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    apply Real.self_le_rpow_of_one_le hBreal
    cases branch <;>
      norm_num [Tao.taoSection5BranchExponent, Tao.taoAlpha]
  have hsourceNonneg : 0 ≤ Tao.taoSection5SourceY B branch :=
    hBreal.trans hsource |>.trans' (by norm_num)
  have hexp :
      1 ≤ Real.exp ((j : ℝ) * ndA5BandBeta B branch) :=
    Real.one_le_exp
      (mul_nonneg (Nat.cast_nonneg j) (ndA5BandBeta_nonneg hB branch))
  unfold ndA5BandLower
  exact hsource.trans
    (by simpa using mul_le_mul_of_nonneg_left hexp hsourceNonneg)

/-- Product-endpoint view of the partition-friendly consecutive carrier. -/
theorem ndA5OddBand_eq_oddHalfOpenRealWindow
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    ndA5OddBand B branch j =
      oddHalfOpenRealWindow (ndA5BandLower B branch j)
        (ndA5BandLower B branch j *
          Real.exp (ndA5BandBeta B branch)) := by
  unfold ndA5OddBand
  rw [ndA5BandLower_succ]

/-- Exact membership in a consecutive A5 band. -/
theorem mem_ndA5OddBand
    {B N j : ℕ} {branch : Tao.TaoSection5SourceBranch} :
    N ∈ ndA5OddBand B branch j ↔
      ndA5BandLower B branch j ≤ (N : ℝ) ∧
        (N : ℝ) < ndA5BandLower B branch (j + 1) ∧ N % 2 = 1 := by
  simpa only [ndA5OddBand] using
    (mem_oddHalfOpenRealWindow
      (z := ndA5BandLower B branch j)
      (u := ndA5BandLower B branch (j + 1)) (N := N))

/-- Membership with the equivalent product upper endpoint. -/
theorem mem_ndA5OddBand_exp_iff
    {B N j : ℕ} {branch : Tao.TaoSection5SourceBranch} :
    N ∈ ndA5OddBand B branch j ↔
      ndA5BandLower B branch j ≤ (N : ℝ) ∧
        (N : ℝ) < ndA5BandLower B branch j *
          Real.exp (ndA5BandBeta B branch) ∧ N % 2 = 1 := by
  rw [mem_ndA5OddBand, ndA5BandLower_succ]

/-- Positive band count gives enough absolute scale for the sharp harmonic
error to be at most `1 / 4`. -/
theorem six_le_ndA5BandLower
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    (6 : ℝ) ≤ ndA5BandLower B branch j := by
  have hwidth : (1 : ℝ) ≤ ndA5BandLogWidth B branch := by
    have hcountOne : 1 ≤ ndA5BandCount B branch := by omega
    rw [← Nat.one_le_floor_iff]
    simpa [ndA5BandCount] using hcountOne
  have hlogY :
      (1000 : ℝ) ≤ Real.log (Tao.taoSection5SourceY B branch) := by
    unfold ndA5BandLogWidth at hwidth
    norm_num [alpha, Tao.taoAlpha] at hwidth ⊢
    linarith
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hY : (6 : ℝ) ≤ Tao.taoSection5SourceY B branch := by
    have hExpFive : (6 : ℝ) ≤ Real.exp 5 := by
      have h := Real.add_one_le_exp (5 : ℝ)
      norm_num at h ⊢
      exact h
    calc
      (6 : ℝ) ≤ Real.exp 5 := hExpFive
      _ ≤ Real.exp (Real.log (Tao.taoSection5SourceY B branch)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Tao.taoSection5SourceY B branch := Real.exp_log hYpos
  have hbeta : 0 ≤ ndA5BandBeta B branch :=
    zero_le_one.trans (ndA5BandBeta_mem_Ico hcount).1
  have hexp : 1 ≤ Real.exp ((j : ℝ) * ndA5BandBeta B branch) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg j) hbeta)
  unfold ndA5BandLower
  exact hY.trans (by
    simpa using mul_le_mul_of_nonneg_left hexp hYpos.le)

/-- There is more than one real unit between consecutive A5 endpoints. -/
theorem ndA5BandLower_add_one_lt_succ
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandLower B branch j + 1 <
      ndA5BandLower B branch (j + 1) := by
  have hz := six_le_ndA5BandLower hB j hcount
  have hbeta : (1 : ℝ) ≤ ndA5BandBeta B branch :=
    (ndA5BandBeta_mem_Ico hcount).1
  have hexpTwo : (2 : ℝ) ≤ Real.exp (ndA5BandBeta B branch) := by
    have := Real.add_one_le_exp (ndA5BandBeta B branch)
    linarith
  rw [ndA5BandLower_succ]
  have hmul := mul_le_mul_of_nonneg_left hexpTwo (by linarith :
    0 ≤ ndA5BandLower B branch j)
  nlinarith

/-- Consecutive A5 endpoints remain strictly separated after natural
ceiling. -/
theorem ndA5BandLower_ceil_lt_ceil_succ
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    Nat.ceil (ndA5BandLower B branch j) <
      Nat.ceil (ndA5BandLower B branch (j + 1)) := by
  apply Nat.lt_ceil.mpr
  exact (Nat.ceil_lt_add_one (by
    linarith [six_le_ndA5BandLower hB j hcount] :
      0 ≤ ndA5BandLower B branch j)).trans
    (ndA5BandLower_add_one_lt_succ hB j hcount)

/-- Sharp flat normalization of one exact A5 band. -/
theorem abs_card_ndA5OddBand_sub_flat_center_lt_one
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    |((ndA5OddBand B branch j).card : ℝ) -
        ndA5BandLower B branch j *
          (Real.exp (ndA5BandBeta B branch) - 1) / 2| < 1 := by
  have hz : 0 ≤ ndA5BandLower B branch j := by
    linarith [six_le_ndA5BandLower hB j hcount]
  have hzu : ndA5BandLower B branch j ≤
      ndA5BandLower B branch (j + 1) :=
    (ndA5BandLower_add_one_lt_succ hB j hcount).le.trans'
      (le_add_of_nonneg_right (by norm_num))
  have h := abs_card_oddHalfOpenRealWindow_sub_half_width_lt_one hz hzu
  have hcenter :
      (ndA5BandLower B branch (j + 1) - ndA5BandLower B branch j) / 2 =
        ndA5BandLower B branch j *
          (Real.exp (ndA5BandBeta B branch) - 1) / 2 := by
    rw [ndA5BandLower_succ_sub]
  simpa only [ndA5OddBand, hcenter] using h

/-- The logarithmic width between consecutive A5 endpoints is exactly
`beta`. -/
theorem ndA5_log_bandLower_succ_sub
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    Real.log (ndA5BandLower B branch (j + 1)) -
        Real.log (ndA5BandLower B branch j) =
      ndA5BandBeta B branch := by
  have hz : 0 < ndA5BandLower B branch j := by
    linarith [six_le_ndA5BandLower hB j hcount]
  rw [ndA5BandLower_succ,
    Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- Sharp harmonic normalization of one exact A5 band. -/
theorem abs_logFinsetMass_ndA5OddBand_sub_half_beta_le
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    |Tao.logFinsetMass (ndA5OddBand B branch j) -
        ndA5BandBeta B branch / 2| ≤
      3 / (2 * ndA5BandLower B branch j) := by
  have hz : 0 < ndA5BandLower B branch j := by
    linarith [six_le_ndA5BandLower hB j hcount]
  have hzu : ndA5BandLower B branch j ≤
      ndA5BandLower B branch (j + 1) :=
    (ndA5BandLower_add_one_lt_succ hB j hcount).le.trans'
      (le_add_of_nonneg_right (by norm_num))
  have hceil := ndA5BandLower_ceil_lt_ceil_succ hB j hcount
  have h := abs_logFinsetMass_oddHalfOpenRealWindow_sub_half_log_width_le
    hz hzu hceil
  rw [ndA5_log_bandLower_succ_sub hB j hcount] at h
  have hcenter : (1 / 2 : ℝ) * ndA5BandBeta B branch =
      ndA5BandBeta B branch / 2 := by ring
  simpa only [ndA5OddBand, hcenter] using h

/-- Convenient weaker harmonic error used by later normalization algebra. -/
theorem abs_logFinsetMass_ndA5OddBand_sub_half_beta_le_two_div
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    |Tao.logFinsetMass (ndA5OddBand B branch j) -
        ndA5BandBeta B branch / 2| ≤
      2 / ndA5BandLower B branch j := by
  have hz : 0 < ndA5BandLower B branch j := by
    linarith [six_le_ndA5BandLower hB j hcount]
  refine (abs_logFinsetMass_ndA5OddBand_sub_half_beta_le
    hB j hcount).trans ?_
  calc
    3 / (2 * ndA5BandLower B branch j) =
        (3 / 2 : ℝ) * (1 / ndA5BandLower B branch j) := by field_simp
    _ ≤ 2 * (1 / ndA5BandLower B branch j) :=
      mul_le_mul_of_nonneg_right (by norm_num) (one_div_nonneg.mpr hz.le)
    _ = 2 / ndA5BandLower B branch j := by ring

/-- Every exact A5 band has logarithmic mass at least one quarter. -/
theorem one_fourth_le_logFinsetMass_ndA5OddBand
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    (1 / 4 : ℝ) ≤ Tao.logFinsetMass (ndA5OddBand B branch j) := by
  have hzSix := six_le_ndA5BandLower hB j hcount
  have hz : 0 < ndA5BandLower B branch j := by linarith
  have hbeta : (1 : ℝ) ≤ ndA5BandBeta B branch :=
    (ndA5BandBeta_mem_Ico hcount).1
  have herr :
      3 / (2 * ndA5BandLower B branch j) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hz)).2
    nlinarith
  have hmass := abs_logFinsetMass_ndA5OddBand_sub_half_beta_le
    hB j hcount
  rw [abs_le] at hmass
  linarith

/-- Positivity form of the A5 band mass floor. -/
theorem logFinsetMass_ndA5OddBand_pos
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    0 < Tao.logFinsetMass (ndA5OddBand B branch j) := by
  linarith [one_fourth_le_logFinsetMass_ndA5OddBand hB j hcount]

/-- The mass floor supplies a point in every exact A5 odd band. -/
theorem ndA5OddBand_nonempty
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    (ndA5OddBand B branch j).Nonempty := by
  have hpos := logFinsetMass_ndA5OddBand_pos hB j hcount
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h] at hpos
  simp [Tao.logFinsetMass] at hpos

/-- Cardinality form of A5 band nonemptiness. -/
theorem ndA5OddBand_card_pos
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    0 < (ndA5OddBand B branch j).card :=
  Finset.card_pos.mpr (ndA5OddBand_nonempty hB j hcount)

end

end ND
end Erdos1135
