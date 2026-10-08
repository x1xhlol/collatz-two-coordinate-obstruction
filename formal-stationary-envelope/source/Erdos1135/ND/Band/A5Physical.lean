/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Band.A5Tube
import Erdos1135.Tao.Section5.PassScheduleFacts
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A5 Physical Band Schedule

This leaf specializes the neutral A5 tube to the exact logarithmic bands of
frozen v10 Part A.  In particular, the band width is not an arbitrary later
historical parameter: for a source scale `y` it is

`((alpha - 1) * log y) / floor ((alpha - 1) * log y)`.

Thus the finite bands form the exact half-open partition before the padded
first-passage window is introduced.  The first public arithmetic target is
the all-window `(t2)` scale packet; tube containment and endpoint-mass support
are downstream consumers.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- The positive passage-time logarithmic scale `log (4/3)`. -/
noncomputable def ndA5LogFourThirds : ℝ :=
  Real.log (4 / 3 : ℝ)

/-- The v10 A5 tube width `C * sqrt (n0 * log n0)`. -/
noncomputable def ndA5TubeWidth (B : ℕ) (C : ℝ) : ℝ :=
  C * Real.sqrt
    ((Tao.taoSection5N0 B : ℝ) * Real.log (Tao.taoSection5N0 B : ℝ))

/-- Scaling the tube constant by `8/3` scales the physical width exactly. -/
theorem ndA5TubeWidth_eight_thirds (B : ℕ) (C : ℝ) :
    ndA5TubeWidth B ((8 / 3 : ℝ) * C) =
      (8 / 3 : ℝ) * ndA5TubeWidth B C := by
  unfold ndA5TubeWidth
  ring

/-- The carrier padding at scale `(8/3) C` is exactly the source `8W`
window around the analytic tube of width `W(C)`. -/
theorem three_mul_ndA5TubeWidth_eight_thirds (B : ℕ) (C : ℝ) :
    3 * ndA5TubeWidth B ((8 / 3 : ℝ) * C) =
      8 * ndA5TubeWidth B C := by
  rw [ndA5TubeWidth_eight_thirds]
  ring

/-- Total logarithmic width of one source block. -/
noncomputable def ndA5BandLogWidth
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : ℝ :=
  (alpha - 1) * Real.log (Tao.taoSection5SourceY B branch)

/-- Number of equal-log-width bands in frozen v10 Part A. -/
noncomputable def ndA5BandCount
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : ℕ :=
  Nat.floor (ndA5BandLogWidth B branch)

/-- Exact common log width of the Part-A bands for one source block. -/
noncomputable def ndA5BandBeta
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : ℝ :=
  ndA5BandLogWidth B branch / (ndA5BandCount B branch : ℝ)

/-- Lower real endpoint `z_j = y * exp (j * beta)` of band `j`. -/
noncomputable def ndA5BandLower
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) : ℝ :=
  Tao.taoSection5SourceY B branch *
    Real.exp ((j : ℝ) * ndA5BandBeta B branch)

/-- Lower real endpoint of the padded first-passage window `J_j`. -/
noncomputable def ndA5PaddedBandLower
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (C : ℝ) (j : ℕ) : ℝ :=
  Real.log (ndA5BandLower B branch j / (B : ℝ)) /
      ndA5LogFourThirds -
    3 * ndA5TubeWidth B C

/-- Upper real endpoint of the padded first-passage window `J_j`. -/
noncomputable def ndA5PaddedBandUpper
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (C : ℝ) (j : ℕ) : ℝ :=
  Real.log
      (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
        (B : ℝ)) /
      ndA5LogFourThirds +
    3 * ndA5TubeWidth B C

/-- The exact inclusive natural padded window `J_j`. -/
noncomputable def ndA5PaddedBandWindow
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (C : ℝ) (j : ℕ) :
    Finset ℕ :=
  Finset.Icc (Nat.ceil (ndA5PaddedBandLower B branch C j))
    (Nat.floor (ndA5PaddedBandUpper B branch C j))

/-- The physical affine phase `log(z_j/M)/log 2`. -/
noncomputable def ndA5PhysicalPhase (z M : ℝ) : ℝ :=
  Real.log (z / M) / Real.log 2

/-- The signed strict physical endpoint level.  `floor + 1`, rather than
ordinary ceiling, is intentional at integral phase.  Consumers must establish
positivity here before passing to the clipped natural wrapper below. -/
noncomputable def ndA5PhysicalLevelInt (A : ℝ) (nu : ℕ) : ℤ :=
  Int.floor (A + (nu : ℝ) * logTwoThree) + 1

/-- The natural strict physical endpoint level, obtained only by clipping the
signed level. -/
noncomputable def ndA5PhysicalLevel (A : ℝ) (nu : ℕ) : ℕ :=
  (ndA5PhysicalLevelInt A nu).toNat

/-- The centered physical displacement
`log M - (log B + m0 * log(4/3))`. -/
noncomputable def ndA5InteriorShift (B : ℕ) (M : ℝ) : ℝ :=
  Real.log M -
    (Real.log B + (Tao.taoSection5M0 B : ℝ) * ndA5LogFourThirds)

/-- Halving a positive endpoint denominator translates its physical phase by
exactly one. -/
theorem ndA5PhysicalPhase_div_two
    {z M : ℝ} (hz : 0 < z) (hM : 0 < M) :
    ndA5PhysicalPhase z (M / 2) = ndA5PhysicalPhase z M + 1 := by
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold ndA5PhysicalPhase
  rw [show z / (M / 2) = (z / M) * 2 by
        field_simp [hM.ne'],
      Real.log_mul (div_ne_zero hz.ne' hM.ne') (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [hlogTwo]

/-- Halving a positive endpoint subtracts `log 2` from the centered physical
shift. -/
theorem ndA5InteriorShift_div_two
    {B : ℕ} {M : ℝ} (hM : 0 < M) :
    ndA5InteriorShift B (M / 2) =
      ndA5InteriorShift B M - Real.log 2 := by
  unfold ndA5InteriorShift
  rw [Real.log_div hM.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Division by an ordinary natural power of two translates physical phase
by the corresponding natural number. -/
theorem ndA5PhysicalPhase_div_two_pow
    {z M : ℝ} (hz : 0 < z) (hM : 0 < M) (r : ℕ) :
    ndA5PhysicalPhase z (M / (2 : ℝ) ^ r) =
      ndA5PhysicalPhase z M + (r : ℝ) := by
  have hpow : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold ndA5PhysicalPhase
  rw [Real.log_div hz.ne' (div_pos hM hpow).ne',
    Real.log_div hz.ne' hM.ne', Real.log_div hM.ne' hpow.ne',
    Real.log_pow]
  field_simp [hlogTwo]
  ring

/-- Division by an ordinary natural power of two subtracts the corresponding
multiple of `log 2` from the centered physical shift. -/
theorem ndA5InteriorShift_div_two_pow
    {B : ℕ} {M : ℝ} (hM : 0 < M) (r : ℕ) :
    ndA5InteriorShift B (M / (2 : ℝ) ^ r) =
      ndA5InteriorShift B M - (r : ℝ) * Real.log 2 := by
  have hpow : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  unfold ndA5InteriorShift
  rw [Real.log_div hM.ne' hpow.ne', Real.log_pow]
  ring

theorem ndA5LogFourThirds_pos :
    0 < ndA5LogFourThirds := by
  unfold ndA5LogFourThirds
  exact Real.log_pos (by norm_num)

/-- The passage-time logarithm is exactly the A5 decrement times `log 2`. -/
theorem ndA5LogFourThirds_eq_phaseDelta_mul_logTwo :
    ndA5LogFourThirds = ndA5PhaseDelta * Real.log 2 := by
  unfold ndA5LogFourThirds ndA5PhaseDelta logTwoThree
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
    (by norm_num : (3 : ℝ) ≠ 0)]
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

/-- Subtracting the signed drift from the physical level gives the checked
strict affine sweep exactly, before any `Int.toNat` clipping. -/
theorem ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep
    (A : ℝ) (nu : ℕ) :
    ndA5PhysicalLevelInt A nu - 2 * (nu : ℤ) =
      ndA5StrictAffineSweep A nu := by
  simpa [ndA5PhysicalLevelInt] using
    intFloor_add_logTwoThree_add_one_sub_two_mul_eq_strictAffineSweep A nu

/-- Exact centered affine phase for a physical band cell.  The shift is
measured at the common step-back time `m0`, while the natural physical time
is `nu + m0`. -/
theorem ndA5PhysicalPhase_sub_phaseDelta_mul_eq_centered
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {M : ℝ}
    (hB : 1 ≤ B) (hM : 0 < M) :
    ndA5PhysicalPhase (ndA5BandLower B branch j) M -
        ndA5PhaseDelta * (nu : ℝ) =
      ndA5PhaseDelta *
        (Real.log (ndA5BandLower B branch j / (B : ℝ)) /
              ndA5LogFourThirds -
            ((nu + Tao.taoSection5M0 B : ℕ) : ℝ) -
          ndA5InteriorShift B M / ndA5LogFourThirds) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hzpos : 0 < ndA5BandLower B branch j := by
    unfold ndA5BandLower
    positivity
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hdelta : ndA5PhaseDelta ≠ 0 := ndA5PhaseDelta_mem_Ioo.1.ne'
  unfold ndA5PhysicalPhase ndA5InteriorShift
  rw [Real.log_div hzpos.ne' hM.ne', Real.log_div hzpos.ne' hBpos.ne',
    ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
  push_cast
  field_simp
  ring

theorem mem_ndA5PaddedBandWindow_iff
    {B j n : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ} :
    n ∈ ndA5PaddedBandWindow B branch C j ↔
      Nat.ceil (ndA5PaddedBandLower B branch C j) ≤ n ∧
        n ≤ Nat.floor (ndA5PaddedBandUpper B branch C j) := by
  simp [ndA5PaddedBandWindow]

private theorem ndA5_log_sourceY_eq_branchExponent_mul_log
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    Real.log (Tao.taoSection5SourceY B branch) =
      Tao.taoSection5BranchExponent branch * Real.log B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Tao.taoSection5SourceY_eq_branch_rpow]
  exact Real.log_rpow hBpos _

private theorem ndA5BandLogWidth_nonneg
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    0 ≤ ndA5BandLogWidth B branch := by
  unfold ndA5BandLogWidth
  exact mul_nonneg (by norm_num [alpha, Tao.taoAlpha])
    (Real.log_nonneg (by
      have hBReal : (1 : ℝ) ≤ B := by exact_mod_cast hB
      cases branch <;>
        exact Real.one_le_rpow hBReal (by norm_num [Tao.taoAlpha])))

theorem ndA5BandBeta_nonneg
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    0 ≤ ndA5BandBeta B branch := by
  unfold ndA5BandBeta
  exact div_nonneg (ndA5BandLogWidth_nonneg hB branch) (Nat.cast_nonneg _)

theorem ndA5BandBeta_mul_count
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandBeta B branch * (ndA5BandCount B branch : ℝ) =
      ndA5BandLogWidth B branch := by
  unfold ndA5BandBeta
  field_simp

/-- The exact Part-A quotient width lies in the source interval `[1,2)` as
soon as there is at least one band. -/
theorem ndA5BandBeta_mem_Ico
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandBeta B branch ∈ Set.Ico (1 : ℝ) 2 := by
  have hcountOne : 1 ≤ ndA5BandCount B branch := hcount
  have hcountReal : (0 : ℝ) < ndA5BandCount B branch := by
    exact_mod_cast hcount
  have hwidthOne : (1 : ℝ) ≤ ndA5BandLogWidth B branch := by
    rw [← Nat.one_le_floor_iff]
    simpa [ndA5BandCount] using hcountOne
  have hfloorLe : (ndA5BandCount B branch : ℝ) ≤
      ndA5BandLogWidth B branch := by
    simpa [ndA5BandCount] using
      Nat.floor_le ((by norm_num : (0 : ℝ) ≤ 1).trans hwidthOne)
  have hwidthLt : ndA5BandLogWidth B branch <
      (ndA5BandCount B branch : ℝ) + 1 := by
    simpa [ndA5BandCount] using
      Nat.lt_floor_add_one (ndA5BandLogWidth B branch)
  have hcountOneReal : (1 : ℝ) ≤ ndA5BandCount B branch := by
    exact_mod_cast hcountOne
  constructor
  · unfold ndA5BandBeta
    exact (le_div_iff₀ hcountReal).2 (by simpa using hfloorLe)
  · unfold ndA5BandBeta
    apply (div_lt_iff₀ hcountReal).2
    linarith

/-- Exact logarithmic location of a Part-A band lower endpoint. -/
theorem ndA5_log_bandLower_div
    {B j : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    Real.log (ndA5BandLower B branch j / (B : ℝ)) =
      (Tao.taoSection5BranchExponent branch - 1) * Real.log B +
        (j : ℝ) * ndA5BandBeta B branch := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  unfold ndA5BandLower
  rw [Real.log_div (mul_ne_zero hYpos.ne' (Real.exp_ne_zero _)) hBpos.ne',
    Real.log_mul hYpos.ne' (Real.exp_ne_zero _), Real.log_exp,
    ndA5_log_sourceY_eq_branchExponent_mul_log hB branch]
  ring

/-- Exact logarithmic location of a Part-A band upper endpoint. -/
theorem ndA5_log_bandUpper_div
    {B j : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    Real.log
        (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
          (B : ℝ)) =
      (Tao.taoSection5BranchExponent branch - 1) * Real.log B +
        ((j : ℝ) + 1) * ndA5BandBeta B branch := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  unfold ndA5BandLower
  rw [Real.log_div
    (mul_ne_zero (mul_ne_zero hYpos.ne' (Real.exp_ne_zero _))
      (Real.exp_ne_zero _)) hBpos.ne',
    Real.log_mul (mul_ne_zero hYpos.ne' (Real.exp_ne_zero _))
      (Real.exp_ne_zero _),
    Real.log_mul hYpos.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_exp, ndA5_log_sourceY_eq_branchExponent_mul_log hB branch]
  ring

private theorem ndA5BandLogWidth_eq
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    ndA5BandLogWidth B branch =
      (alpha - 1) * Tao.taoSection5BranchExponent branch * Real.log B := by
  unfold ndA5BandLogWidth
  rw [ndA5_log_sourceY_eq_branchExponent_mul_log hB branch]
  ring

/-- Every valid exact Part-A band stays between its source scale and the
outer endpoint `y^alpha`, at the level of logarithmic passage time. -/
theorem ndA5_valid_band_log_range
    {B j : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hj : j < ndA5BandCount B branch) :
    (Tao.taoSection5BranchExponent branch - 1) * Real.log B ≤
        Real.log (ndA5BandLower B branch j / (B : ℝ)) ∧
      Real.log
          (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
            (B : ℝ)) ≤
        (alpha * Tao.taoSection5BranchExponent branch - 1) * Real.log B := by
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hbeta := ndA5BandBeta_nonneg hB branch
  have hjReal : ((j : ℝ) + 1) ≤ (ndA5BandCount B branch : ℝ) := by
    exact_mod_cast (show j + 1 ≤ ndA5BandCount B branch by omega)
  have hbetaRange :
      ((j : ℝ) + 1) * ndA5BandBeta B branch ≤
        ndA5BandLogWidth B branch := by
    calc
      ((j : ℝ) + 1) * ndA5BandBeta B branch ≤
          (ndA5BandCount B branch : ℝ) * ndA5BandBeta B branch :=
        mul_le_mul_of_nonneg_right hjReal hbeta
      _ = ndA5BandLogWidth B branch := by
        rw [mul_comm, ndA5BandBeta_mul_count hcount]
  rw [ndA5_log_bandLower_div hB branch,
    ndA5_log_bandUpper_div hB branch]
  constructor
  · have hjbeta : 0 ≤ (j : ℝ) * ndA5BandBeta B branch :=
      mul_nonneg (Nat.cast_nonneg j) hbeta
    linarith
  · rw [ndA5BandLogWidth_eq hB branch] at hbetaRange
    nlinarith

/-- An intrinsic full-tube index at width `C` lies in a possibly wider
physical padded band window at width `Cpad` once the exact shift and rounding
margin fit inside the latter's `3W` padding. -/
theorem ndA5FullTube_shift_mem_paddedBandWindow_of_crossWidthMargin
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C Cpad M S : ℝ}
    (hB : 1 ≤ B) (hM : 0 < M)
    (hshift : |ndA5InteriorShift B M| ≤ S)
    (hmargin :
      S / ndA5LogFourThirds +
          (ndA5TubeWidth B C + 1) / ndA5PhaseDelta ≤
        3 * ndA5TubeWidth B Cpad)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    nu + Tao.taoSection5M0 B ∈
      ndA5PaddedBandWindow B branch Cpad j := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let Wpad := ndA5TubeWidth B Cpad
  let s := ndA5InteriorShift B M
  let n := nu + Tao.taoSection5M0 B
  let N := Real.log (ndA5BandLower B branch j / (B : ℝ)) /
    ndA5LogFourThirds
  have hnu' : nu ∈ ndA5FullTube A W := by
    simpa [A, W] using hnu
  have htube : |(ndA5StrictAffineSweep A nu : ℝ)| < W :=
    (Finset.mem_filter.mp hnu').2
  have htubeBounds := abs_lt.mp htube
  have hresidual := ndA5StrictAffineSweep_sub_affine_mem_Ioc A nu
  have haffine : |A - ndA5PhaseDelta * (nu : ℝ)| < W + 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hcenterEq :
      A - ndA5PhaseDelta * (nu : ℝ) =
        ndA5PhaseDelta *
          (N - (n : ℝ) - s / ndA5LogFourThirds) := by
    simpa [A, N, n, s] using
      (ndA5PhysicalPhase_sub_phaseDelta_mul_eq_centered
        (B := B) (j := j) (nu := nu) (branch := branch) (M := M) hB hM)
  rw [hcenterEq, abs_mul,
    abs_of_pos ndA5PhaseDelta_mem_Ioo.1] at haffine
  have hcenter :
      |N - (n : ℝ) - s / ndA5LogFourThirds| <
        (W + 1) / ndA5PhaseDelta := by
    apply (lt_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).2
    simpa [mul_comm] using haffine
  have hshift' : |s| ≤ S := by
    simpa [s] using hshift
  have hshiftBounds := abs_le.mp hshift'
  have hshiftDivLower :
      (-S) / ndA5LogFourThirds ≤
        s / ndA5LogFourThirds :=
    div_le_div_of_nonneg_right hshiftBounds.1 ndA5LogFourThirds_pos.le
  have hshiftDivUpper :
      s / ndA5LogFourThirds ≤
        S / ndA5LogFourThirds :=
    div_le_div_of_nonneg_right hshiftBounds.2 ndA5LogFourThirds_pos.le
  have hnegShiftDivUpper :
      -(s / ndA5LogFourThirds) ≤
        S / ndA5LogFourThirds := by
    calc
      -(s / ndA5LogFourThirds) ≤
          -((-S) / ndA5LogFourThirds) :=
        neg_le_neg hshiftDivLower
      _ = S / ndA5LogFourThirds := by ring
  have hmargin' :
      S / ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta ≤ 3 * Wpad := by
    simpa [W, Wpad] using hmargin
  have hcenterBounds := abs_lt.mp hcenter
  have hnLower : N - 3 * Wpad ≤ (n : ℝ) := by
    linarith
  have hnUpperBase : (n : ℝ) ≤ N + 3 * Wpad := by
    linarith [hcenterBounds.1, hnegShiftDivUpper, hmargin']
  have hlogOrder :
      Real.log (ndA5BandLower B branch j / (B : ℝ)) ≤
        Real.log
          (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
            (B : ℝ)) := by
    rw [ndA5_log_bandLower_div hB branch,
      ndA5_log_bandUpper_div hB branch]
    nlinarith [ndA5BandBeta_nonneg hB branch]
  have hNUpper :
      N ≤
        Real.log
            (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
              (B : ℝ)) /
          ndA5LogFourThirds := by
    dsimp [N]
    exact div_le_div_of_nonneg_right hlogOrder ndA5LogFourThirds_pos.le
  apply mem_ndA5PaddedBandWindow_iff.mpr
  constructor
  · apply Nat.ceil_le.mpr
    simpa [ndA5PaddedBandLower, N, Wpad, n] using hnLower
  · apply Nat.le_floor
    unfold ndA5PaddedBandUpper
    change (n : ℝ) ≤ _
    linarith

/-- The original same-width containment surface, retained as the exact
specialization of cross-width containment used by the physical lane. -/
theorem ndA5FullTube_shift_mem_paddedBandWindow_of_margin
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hM : 0 < M)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hmargin :
      ((4 / 25 : ℝ) * ndA5TubeWidth B C) / ndA5LogFourThirds +
          (ndA5TubeWidth B C + 1) / ndA5PhaseDelta ≤
        3 * ndA5TubeWidth B C)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    nu + Tao.taoSection5M0 B ∈
      ndA5PaddedBandWindow B branch C j :=
  ndA5FullTube_shift_mem_paddedBandWindow_of_crossWidthMargin
    hB hM hshift hmargin hnu

/-- The signed and natural endpoint facts needed before endpoint-mass support
may be discussed. -/
structure NDA5PhysicalLevelFacts (A : ℝ) (nu : ℕ) : Prop where
  nu_lt_int : (nu : ℤ) < ndA5PhysicalLevelInt A nu
  int_lt_three_mul : ndA5PhysicalLevelInt A nu < 3 * (nu : ℤ)
  int_pos : 0 < ndA5PhysicalLevelInt A nu
  nat_cast_eq : (ndA5PhysicalLevel A nu : ℤ) =
    ndA5PhysicalLevelInt A nu
  nu_le_nat : nu ≤ ndA5PhysicalLevel A nu
  nat_le_three_mul : ndA5PhysicalLevel A nu ≤ 3 * nu

/-- Inside the intrinsic tube, the `(t2)` width comparison makes the signed
physical level positive and its natural wrapper lossless. -/
theorem ndA5PhysicalLevelFacts_of_mem_fullTube
    {A W : ℝ} {nu : ℕ} (hnuPos : 0 < nu)
    (hWle : W ≤ (nu : ℝ) / 8)
    (hnu : nu ∈ ndA5FullTube A W) :
    NDA5PhysicalLevelFacts A nu := by
  have htube : |(ndA5StrictAffineSweep A nu : ℝ)| < W :=
    (Finset.mem_filter.mp hnu).2
  have htubeLower := (abs_lt.mp htube).1
  have htubeUpper := (abs_lt.mp htube).2
  have hbridge :=
    ndA5PhysicalLevelInt_sub_two_mul_eq_strictAffineSweep A nu
  have hbridgeReal := congrArg (fun z : ℤ => (z : ℝ)) hbridge
  push_cast at hbridgeReal
  have hnuReal : (0 : ℝ) < nu := by exact_mod_cast hnuPos
  have hnuLevelReal :
      (nu : ℝ) < (ndA5PhysicalLevelInt A nu : ℝ) := by
    linarith
  have hnuLevelInt :
      (nu : ℤ) < ndA5PhysicalLevelInt A nu := by
    exact_mod_cast hnuLevelReal
  have hlevelUpperReal :
      (ndA5PhysicalLevelInt A nu : ℝ) < 3 * (nu : ℝ) := by
    linarith [htubeUpper]
  have hlevelUpperInt :
      ndA5PhysicalLevelInt A nu < 3 * (nu : ℤ) := by
    exact_mod_cast hlevelUpperReal
  have hlevelPos : 0 < ndA5PhysicalLevelInt A nu :=
    (Int.natCast_nonneg nu).trans_lt hnuLevelInt
  have hnatCast : (ndA5PhysicalLevel A nu : ℤ) =
      ndA5PhysicalLevelInt A nu := by
    unfold ndA5PhysicalLevel
    exact Int.toNat_of_nonneg hlevelPos.le
  have hnuLeNat : nu ≤ ndA5PhysicalLevel A nu := by
    exact_mod_cast (hnuLevelInt.le.trans_eq hnatCast.symm)
  have hnatLeThree : ndA5PhysicalLevel A nu ≤ 3 * nu := by
    have hcast : (ndA5PhysicalLevel A nu : ℤ) ≤ (3 * nu : ℕ) := by
      rw [hnatCast]
      exact_mod_cast hlevelUpperInt.le
    exact_mod_cast hcast
  exact
    { nu_lt_int := hnuLevelInt
      int_lt_three_mul := hlevelUpperInt
      int_pos := hlevelPos
      nat_cast_eq := hnatCast
      nu_le_nat := hnuLeNat
      nat_le_three_mul := hnatLeThree }

private theorem ndA5LogFourThirds_lower :
    (287682 / 1000000 : ℝ) < ndA5LogFourThirds := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -(1 / 3 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ, ndA5LogFourThirds] at h ⊢
  rw [abs_le] at h
  norm_num at h
  linarith

private theorem ndA5LogFourThirds_upper :
    ndA5LogFourThirds < (2876821 / 10000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -(1 / 3 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ, ndA5LogFourThirds] at h ⊢
  rw [abs_le] at h
  norm_num at h
  linarith

private theorem ndA5PhaseDelta_inv_lt_two_point_four_one :
    (1 : ℝ) / ndA5PhaseDelta < 241 / 100 := by
  have hlogTwoUpper : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    exact h
  have hinv : (1 : ℝ) / ndA5PhaseDelta =
      Real.log 2 / ndA5LogFourThirds := by
    rw [ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hinv]
  apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
  nlinarith [ndA5LogFourThirds_lower]

/-- The strict first-passage logarithmic errors fit inside the frozen `3W`
padding once the physical tube has reached width six. -/
theorem ndA5FirstPassagePaddingMargin
    {W : ℝ} (hW : 6 ≤ W) :
    W / ndA5PhaseDelta ≤ 3 * W ∧
      (W + 1) / ndA5PhaseDelta + 1 ≤ 3 * W := by
  have hW0 : 0 ≤ W := by linarith
  have hW1 : 0 ≤ W + 1 := by linarith
  have hfirst :
      W / ndA5PhaseDelta ≤ (241 / 100 : ℝ) * W := by
    rw [show W / ndA5PhaseDelta =
      ((1 : ℝ) / ndA5PhaseDelta) * W by ring]
    exact mul_le_mul_of_nonneg_right
      ndA5PhaseDelta_inv_lt_two_point_four_one.le hW0
  have hsecond :
      (W + 1) / ndA5PhaseDelta ≤
        (241 / 100 : ℝ) * (W + 1) := by
    rw [show (W + 1) / ndA5PhaseDelta =
      ((1 : ℝ) / ndA5PhaseDelta) * (W + 1) by ring]
    exact mul_le_mul_of_nonneg_right
      ndA5PhaseDelta_inv_lt_two_point_four_one.le hW1
  constructor <;> nlinarith

private theorem ndA5InteriorExcursionCoefficient_lt :
    (4 / 25 : ℝ) / ndA5LogFourThirds + 1 / ndA5PhaseDelta <
      3707 / 1250 := by
  have hlogTwoUpper : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    exact h
  have hinv : (1 : ℝ) / ndA5PhaseDelta =
      Real.log 2 / ndA5LogFourThirds := by
    rw [ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hinv, ← add_div]
  apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
  nlinarith [ndA5LogFourThirds_lower]

/-- The visible source guard `C ≥ 1/2` and the all-window logarithmic scale
give the stronger width needed to retain the original padded carrier after the
first phase shift. -/
theorem ndA5TubeWidth_ge_one_hundred_forty_two
    {B : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    (142 : ℝ) ≤ ndA5TubeWidth B C := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoLtOne : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hscale :
      (30000 : ℝ) < Real.log B / (10 * Real.log 2) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hlogTwoPos)).2
    nlinarith
  have hn0Lower := Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hn0Lower' :
      (29999 : ℝ) < (Tao.taoSection5N0 B : ℝ) := by
    linarith
  have hn0Nat : 30000 ≤ Tao.taoSection5N0 B := by
    have : 29999 < Tao.taoSection5N0 B := by exact_mod_cast hn0Lower'
    omega
  have hn0Cast : (30000 : ℝ) ≤ Tao.taoSection5N0 B := by
    exact_mod_cast hn0Nat
  have hn0Sixteen : (16 : ℝ) ≤ Tao.taoSection5N0 B := by
    exact_mod_cast (show 16 ≤ Tao.taoSection5N0 B by omega)
  have hlogTwoLower : (69 / 100 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlogN0 : (69 / 25 : ℝ) ≤
      Real.log (Tao.taoSection5N0 B : ℝ) := by
    have hlogSixteen :
        Real.log (16 : ℝ) ≤
          Real.log (Tao.taoSection5N0 B : ℝ) :=
      Real.log_le_log (by norm_num) hn0Sixteen
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num,
      Real.log_pow] at hlogSixteen
    norm_num at hlogSixteen ⊢
    nlinarith
  have hproduct : (82800 : ℝ) ≤
      (Tao.taoSection5N0 B : ℝ) *
        Real.log (Tao.taoSection5N0 B : ℝ) := by
    calc
      (82800 : ℝ) = 30000 * (69 / 25 : ℝ) := by norm_num
      _ ≤ (Tao.taoSection5N0 B : ℝ) * (69 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_right hn0Cast (by norm_num)
      _ ≤ (Tao.taoSection5N0 B : ℝ) *
          Real.log (Tao.taoSection5N0 B : ℝ) :=
        mul_le_mul_of_nonneg_left hlogN0 (Nat.cast_nonneg _)
  have hsqrt : (284 : ℝ) ≤ Real.sqrt
      ((Tao.taoSection5N0 B : ℝ) *
        Real.log (Tao.taoSection5N0 B : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  unfold ndA5TubeWidth
  calc
    (142 : ℝ) = (1 / 2 : ℝ) * 284 := by norm_num
    _ ≤ C * Real.sqrt
        ((Tao.taoSection5N0 B : ℝ) *
          Real.log (Tao.taoSection5N0 B : ℝ)) :=
      mul_le_mul hC hsqrt (by norm_num) (by linarith)

/-- The earlier rounding-scale width bound, retained as a stable public
interface for existing physical consumers. -/
theorem ndA5TubeWidth_ge_seventy_one
    {B : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    (71 : ℝ) ≤ ndA5TubeWidth B C := by
  linarith [ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB]

/-- The source scale discharges the exact scalar margin used by physical
full-tube containment. -/
theorem ndA5InteriorContainmentMargin
    {B : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    ((4 / 25 : ℝ) * ndA5TubeWidth B C) / ndA5LogFourThirds +
          (ndA5TubeWidth B C + 1) / ndA5PhaseDelta ≤
        3 * ndA5TubeWidth B C := by
  let W := ndA5TubeWidth B C
  have hW : (71 : ℝ) ≤ W := by
    simpa [W] using ndA5TubeWidth_ge_seventy_one hC hlogB
  have hW0 : 0 ≤ W := by linarith
  have hcoefMul :
      ((4 / 25 : ℝ) / ndA5LogFourThirds + 1 / ndA5PhaseDelta) * W ≤
        (3707 / 1250 : ℝ) * W :=
    mul_le_mul_of_nonneg_right ndA5InteriorExcursionCoefficient_lt.le hW0
  change ((4 / 25 : ℝ) * W) / ndA5LogFourThirds +
      (W + 1) / ndA5PhaseDelta ≤ 3 * W
  have halgebra :
      ((4 / 25 : ℝ) * W) / ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta =
        ((4 / 25 : ℝ) / ndA5LogFourThirds + 1 / ndA5PhaseDelta) * W +
          1 / ndA5PhaseDelta := by
    ring
  rw [halgebra]
  nlinarith [ndA5PhaseDelta_inv_lt_two_point_four_one]

/-- The original same-width padded carrier also absorbs the `log 2`
displacement created by the first neighboring phase. -/
theorem ndA5FirstShiftContainmentMargin
    {B : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    ((4 / 25 : ℝ) * ndA5TubeWidth B C + Real.log 2) /
          ndA5LogFourThirds +
        (ndA5TubeWidth B C + 1) / ndA5PhaseDelta ≤
      3 * ndA5TubeWidth B C := by
  let W := ndA5TubeWidth B C
  have hW : (142 : ℝ) ≤ W := by
    simpa [W] using
      ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hW0 : 0 ≤ W := by linarith
  have hcoefMul :
      ((4 / 25 : ℝ) / ndA5LogFourThirds +
          1 / ndA5PhaseDelta) * W ≤
        (3707 / 1250 : ℝ) * W :=
    mul_le_mul_of_nonneg_right
      ndA5InteriorExcursionCoefficient_lt.le hW0
  have hlogRatio :
      Real.log 2 / ndA5LogFourThirds =
        1 / ndA5PhaseDelta := by
    rw [ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hconstant :
      (2 : ℝ) / ndA5PhaseDelta ≤ 241 / 50 := by
    rw [show (2 : ℝ) / ndA5PhaseDelta =
      2 * (1 / ndA5PhaseDelta) by ring]
    nlinarith [ndA5PhaseDelta_inv_lt_two_point_four_one]
  have hslack :
      (3707 / 1250 : ℝ) * W + 241 / 50 + 81 / 1250 ≤
        3 * W := by
    nlinarith [hW]
  change ((4 / 25 : ℝ) * W + Real.log 2) /
        ndA5LogFourThirds +
      (W + 1) / ndA5PhaseDelta ≤ 3 * W
  have halgebra :
      ((4 / 25 : ℝ) * W + Real.log 2) /
            ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta =
        ((4 / 25 : ℝ) / ndA5LogFourThirds +
            1 / ndA5PhaseDelta) * W +
          2 / ndA5PhaseDelta := by
    calc
      _ = ((4 / 25 : ℝ) / ndA5LogFourThirds +
              1 / ndA5PhaseDelta) * W +
            Real.log 2 / ndA5LogFourThirds +
            1 / ndA5PhaseDelta := by ring
      _ = ((4 / 25 : ℝ) / ndA5LogFourThirds +
              1 / ndA5PhaseDelta) * W +
            2 / ndA5PhaseDelta := by
        rw [hlogRatio]
        ring
  rw [halgebra]
  nlinarith [hcoefMul, hconstant, hslack]

/-- The single widened-carrier estimate used by the first two shifted analytic
packets.  All decimal logarithm estimates remain private behind this `8W`
surface. -/
theorem ndA5WideContainmentMargin
    {B : ℕ} {C : ℝ} (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    ((3 / 2 : ℝ) * ndA5TubeWidth B C + 2 * Real.log 2) /
          ndA5LogFourThirds +
        (ndA5TubeWidth B C + 1) / ndA5PhaseDelta ≤
      8 * ndA5TubeWidth B C := by
  let W := ndA5TubeWidth B C
  have hW : (71 : ℝ) ≤ W := by
    simpa [W] using ndA5TubeWidth_ge_seventy_one hC hlogB
  have hW0 : 0 ≤ W := by linarith
  have hfirst :
      (3 / 2 : ℝ) / ndA5LogFourThirds < 522 / 100 := by
    apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
    nlinarith [ndA5LogFourThirds_lower]
  have hcoef :
      (3 / 2 : ℝ) / ndA5LogFourThirds +
          1 / ndA5PhaseDelta < 763 / 100 := by
    nlinarith [ndA5PhaseDelta_inv_lt_two_point_four_one]
  have hcoefMul :
      ((3 / 2 : ℝ) / ndA5LogFourThirds +
          1 / ndA5PhaseDelta) * W ≤
        (763 / 100 : ℝ) * W :=
    mul_le_mul_of_nonneg_right hcoef.le hW0
  have hlogRatio :
      Real.log 2 / ndA5LogFourThirds = 1 / ndA5PhaseDelta := by
    rw [ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
    field_simp [ndA5PhaseDelta_mem_Ioo.1.ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have halgebra :
      ((3 / 2 : ℝ) * W + 2 * Real.log 2) / ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta =
        ((3 / 2 : ℝ) / ndA5LogFourThirds +
            1 / ndA5PhaseDelta) * W +
          3 / ndA5PhaseDelta := by
    calc
      ((3 / 2 : ℝ) * W + 2 * Real.log 2) / ndA5LogFourThirds +
          (W + 1) / ndA5PhaseDelta =
          ((3 / 2 : ℝ) / ndA5LogFourThirds +
              1 / ndA5PhaseDelta) * W +
            2 * (Real.log 2 / ndA5LogFourThirds) +
              1 / ndA5PhaseDelta := by ring
      _ = ((3 / 2 : ℝ) / ndA5LogFourThirds +
              1 / ndA5PhaseDelta) * W +
            3 / ndA5PhaseDelta := by rw [hlogRatio]; ring
  have hconstant :
      (3 : ℝ) / ndA5PhaseDelta < 723 / 100 := by
    rw [show (3 : ℝ) / ndA5PhaseDelta =
      3 * (1 / ndA5PhaseDelta) by ring]
    nlinarith [ndA5PhaseDelta_inv_lt_two_point_four_one]
  change ((3 / 2 : ℝ) * W + 2 * Real.log 2) /
          ndA5LogFourThirds +
        (W + 1) / ndA5PhaseDelta ≤ 8 * W
  rw [halgebra]
  nlinarith

/-- Source-facing physical containment with the scalar margin derived from
the visible tube constant and logarithmic-scale guards. -/
theorem ndA5FullTube_shift_mem_paddedBandWindow
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hC : (1 / 2 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B) (hM : 0 < M)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    nu + Tao.taoSection5M0 B ∈
      ndA5PaddedBandWindow B branch C j :=
  ndA5FullTube_shift_mem_paddedBandWindow_of_margin
    hB hM hshift (ndA5InteriorContainmentMargin hC hlogB) hnu

private theorem one_div_thousand_div_ndA5LogFourThirds_gt :
    (3476 / 1000000 : ℝ) < (1 / 1000 : ℝ) / ndA5LogFourThirds := by
  apply (lt_div_iff₀ ndA5LogFourThirds_pos).2
  have hupper := ndA5LogFourThirds_upper
  norm_num at hupper ⊢
  nlinarith

private theorem alpha_cube_sub_one_div_ndA5LogFourThirds_lt :
    (alpha ^ 3 - 1) / ndA5LogFourThirds < (10439 / 1000000 : ℝ) := by
  apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
  have hlower := ndA5LogFourThirds_lower
  norm_num [alpha, Tao.taoAlpha] at hlower ⊢
  nlinarith

/-- The scale facts needed before specializing the neutral tube to a physical
band.  The printed decimal bounds remain visible, while the sharp upper
ratio is proved from the exact `alpha^3` endpoint rather than the rounded
`nu <= 0.0105 log B` display. -/
structure NDA5T2ScaleFacts (B n : ℕ) (C : ℝ) : Prop where
  nu_pos : 0 < n - Tao.taoSection5M0 B
  nu_lower :
    (340 / 100000 : ℝ) * Real.log B ≤
      (n - Tao.taoSection5M0 B : ℕ)
  nu_upper :
    ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
      (105 / 10000 : ℝ) * Real.log B
  n0_div_nu_lower :
    (1374 / 100 : ℝ) ≤
      (Tao.taoSection5N0 B : ℝ) /
        (n - Tao.taoSection5M0 B : ℕ)
  n0_div_nu_upper :
    (Tao.taoSection5N0 B : ℝ) /
        (n - Tao.taoSection5M0 B : ℕ) ≤
      (4244 / 100 : ℝ)
  width_le_nu_div_eight :
    ndA5TubeWidth B C ≤
      (n - Tao.taoSection5M0 B : ℕ) / 8

/-- A `(t2)` scale packet can be narrowed to any smaller tube width.  Its
first five fields are independent of the tube constant. -/
theorem NDA5T2ScaleFacts.mono_width
    {B n : ℕ} {Csmall Cbig : ℝ}
    (h : NDA5T2ScaleFacts B n Cbig)
    (hwidth : ndA5TubeWidth B Csmall ≤ ndA5TubeWidth B Cbig) :
    NDA5T2ScaleFacts B n Csmall where
  nu_pos := h.nu_pos
  nu_lower := h.nu_lower
  nu_upper := h.nu_upper
  n0_div_nu_lower := h.n0_div_nu_lower
  n0_div_nu_upper := h.n0_div_nu_upper
  width_le_nu_div_eight := hwidth.trans h.width_le_nu_div_eight

/-- A `(t2)` point lies after the common step-back time. -/
theorem NDA5T2ScaleFacts.m0_le
    {B n : ℕ} {C : ℝ}
    (h : NDA5T2ScaleFacts B n C) :
    Tao.taoSection5M0 B ≤ n := by
  have hnu := h.nu_pos
  omega

/-- The shifted `(t2)` horizon remains inside the common `n0` prefix. -/
theorem NDA5T2ScaleFacts.sub_le_n0
    {B n : ℕ} {C : ℝ}
    (h : NDA5T2ScaleFacts B n C) :
    n - Tao.taoSection5M0 B ≤ Tao.taoSection5N0 B := by
  have hnuPos :
      (0 : ℝ) < ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    exact_mod_cast h.nu_pos
  have hn0Mul :
      (1374 / 100 : ℝ) *
          ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) :=
    (le_div_iff₀ hnuPos).mp h.n0_div_nu_lower
  have hcast :
      ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) := by
    calc
      ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
          (1374 / 100 : ℝ) *
            ((n - Tao.taoSection5M0 B : ℕ) : ℝ) :=
        by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              (show (1 : ℝ) ≤ 1374 / 100 by norm_num) hnuPos.le
      _ ≤ (Tao.taoSection5N0 B : ℝ) := hn0Mul
  exact_mod_cast hcast

/-- Every source-guarded `(t2)` time itself lies below `n0`. -/
theorem NDA5T2ScaleFacts.le_n0
    {B n : ℕ} {C : ℝ}
    (h : NDA5T2ScaleFacts B n C) (hB : 1 ≤ B) :
    n ≤ Tao.taoSection5N0 B := by
  have hm0n : Tao.taoSection5M0 B ≤ n := h.m0_le
  have hlogB0 : 0 ≤ Real.log B :=
    Real.log_nonneg (by exact_mod_cast hB)
  have hm0Cast :
      (Tao.taoSection5M0 B : ℝ) ≤ Real.log B / 100000 := by
    rw [Tao.taoSection5M0_eq_floor_log]
    exact Nat.floor_le (div_nonneg hlogB0 (by norm_num))
  have hm0LeNuCast :
      (Tao.taoSection5M0 B : ℝ) ≤
        ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    calc
      (Tao.taoSection5M0 B : ℝ) ≤ Real.log B / 100000 := hm0Cast
      _ = (1 / 100000 : ℝ) * Real.log B := by ring
      _ ≤ (340 / 100000 : ℝ) * Real.log B :=
        mul_le_mul_of_nonneg_right (by norm_num) hlogB0
      _ ≤ ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := h.nu_lower
  have hm0LeNu :
      Tao.taoSection5M0 B ≤ n - Tao.taoSection5M0 B := by
    exact_mod_cast hm0LeNuCast
  have hnuPos :
      (0 : ℝ) < ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    exact_mod_cast h.nu_pos
  have hn0Mul :
      (1374 / 100 : ℝ) *
          ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) :=
    (le_div_iff₀ hnuPos).mp h.n0_div_nu_lower
  have htwoNuCast :
      (2 : ℝ) * ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) := by
    calc
      (2 : ℝ) * ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
          (1374 / 100 : ℝ) *
            ((n - Tao.taoSection5M0 B : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnuPos.le
      _ ≤ (Tao.taoSection5N0 B : ℝ) := hn0Mul
  have htwoNu :
      2 * (n - Tao.taoSection5M0 B) ≤ Tao.taoSection5N0 B := by
    exact_mod_cast htwoNuCast
  omega

private theorem ndA5_branchExponent_bounds
    (branch : Tao.TaoSection5SourceBranch) :
    (1 / 1000 : ℝ) ≤ Tao.taoSection5BranchExponent branch - 1 ∧
      alpha * Tao.taoSection5BranchExponent branch - 1 ≤ alpha ^ 3 - 1 := by
  cases branch <;> norm_num [alpha, Tao.taoAlpha,
    Tao.taoSection5BranchExponent]

/-- Quantitative lower room of the padded physical window above the common
step-back time.  This is an endpoint statement, so it remains meaningful even
before choosing a member of the window. -/
theorem ndA5PaddedBandLower_sub_m0_lower_of_guards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    (340 / 100000 : ℝ) * Real.log B ≤
      ndA5PaddedBandLower B branch C j -
        (Tao.taoSection5M0 B : ℝ) := by
  have hlogB0 : 0 ≤ Real.log B := by linarith
  have hband := ndA5_valid_band_log_range hB branch hj
  have hexponents := ndA5_branchExponent_bounds branch
  have hcoeff := one_div_thousand_div_ndA5LogFourThirds_gt
  have hm0 : (Tao.taoSection5M0 B : ℝ) ≤
      (1 / 100000 : ℝ) * Real.log B := by
    rw [Tao.taoSection5M0_eq_floor_log]
    have hfloor := Nat.floor_le
      (by positivity : (0 : ℝ) ≤ Real.log B / 100000)
    convert hfloor using 1; ring
  have hlowerScaled :
      (1 / 1000 : ℝ) * Real.log B / ndA5LogFourThirds ≤
        Real.log (ndA5BandLower B branch j / (B : ℝ)) /
          ndA5LogFourThirds := by
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hexponents.1 hlogB0).trans hband.1)
      ndA5LogFourThirds_pos.le
  have hcoeffScaled :
      (3476 / 1000000 : ℝ) * Real.log B ≤
        ((1 / 1000 : ℝ) / ndA5LogFourThirds) * Real.log B :=
    mul_le_mul_of_nonneg_right hcoeff.le hlogB0
  have hlowerScaled' :
      ((1 / 1000 : ℝ) / ndA5LogFourThirds) * Real.log B ≤
        Real.log (ndA5BandLower B branch j / (B : ℝ)) /
          ndA5LogFourThirds := by
    calc
      ((1 / 1000 : ℝ) / ndA5LogFourThirds) * Real.log B =
          (1 / 1000 : ℝ) * Real.log B / ndA5LogFourThirds := by ring
      _ ≤ _ := hlowerScaled
  unfold ndA5PaddedBandLower
  norm_num at hcoeffScaled hpadding ⊢
  linarith

/-- The padded window starts strictly after `m0`; hence its total natural
definition cannot make time zero usable at the physical consumer. -/
theorem ndA5M0_lt_ceil_paddedBandLower_of_guards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch) :
    Tao.taoSection5M0 B < Nat.ceil (ndA5PaddedBandLower B branch C j) := by
  apply Nat.lt_ceil.mpr
  have hlower := ndA5PaddedBandLower_sub_m0_lower_of_guards
    hB hlogB hpadding hj
  nlinarith

/-- The interior physical cell has a genuine intrinsic tube point.  The
canonical witness is the floor of the positive affine center; its strict
selector is exactly one. -/
theorem ndA5FullTube_nonempty_of_interior_guards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch) :
    (ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)).Nonempty := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  let s := ndA5InteriorShift B M
  let N := Real.log (ndA5BandLower B branch j / (B : ℝ)) /
    ndA5LogFourThirds
  have hW : (71 : ℝ) ≤ W := by
    simpa [W] using ndA5TubeWidth_ge_seventy_one hC hlogB
  have hWpos : 0 < W := by linarith
  have hroom := ndA5PaddedBandLower_sub_m0_lower_of_guards
    hB hlogB hpadding hj
  have hroom' :
      (1020 : ℝ) ≤ N - 3 * W - (Tao.taoSection5M0 B : ℝ) := by
    have hscale : (1020 : ℝ) ≤
        (340 / 100000 : ℝ) * Real.log B := by
      nlinarith
    simpa [ndA5PaddedBandLower, N, W] using hscale.trans hroom
  have hshift' : |s| ≤ (4 / 25 : ℝ) * W := by
    simpa [s, W] using hshift
  have hshiftUpper := (abs_le.mp hshift').2
  have hshiftDivUpper :
      s / ndA5LogFourThirds ≤
        ((4 / 25 : ℝ) * W) / ndA5LogFourThirds :=
    div_le_div_of_nonneg_right hshiftUpper ndA5LogFourThirds_pos.le
  have hcoef : (4 / 25 : ℝ) / ndA5LogFourThirds < 3 := by
    apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
    nlinarith [ndA5LogFourThirds_lower]
  have hcoefMul :
      ((4 / 25 : ℝ) / ndA5LogFourThirds) * W ≤ 3 * W :=
    mul_le_mul_of_nonneg_right hcoef.le hWpos.le
  have hshiftDivThree : s / ndA5LogFourThirds ≤ 3 * W := by
    calc
      s / ndA5LogFourThirds ≤
          ((4 / 25 : ℝ) * W) / ndA5LogFourThirds := hshiftDivUpper
      _ = ((4 / 25 : ℝ) / ndA5LogFourThirds) * W := by ring
      _ ≤ 3 * W := hcoefMul
  have hcenterPos :
      0 < N - (Tao.taoSection5M0 B : ℝ) -
        s / ndA5LogFourThirds := by
    linarith
  have hcenterEq :=
    ndA5PhysicalPhase_sub_phaseDelta_mul_eq_centered
      (B := B) (j := j) (nu := 0) (branch := branch) (M := M) hB hM
  have hAeq :
      A = ndA5PhaseDelta *
        (N - (Tao.taoSection5M0 B : ℝ) -
          s / ndA5LogFourThirds) := by
    simpa [A, N, s] using hcenterEq
  have hApos : 0 < A := by
    rw [hAeq]
    exact mul_pos ndA5PhaseDelta_mem_Ioo.1 hcenterPos
  let q := Nat.floor (A / ndA5PhaseDelta)
  have hcenterNonneg : 0 ≤ A / ndA5PhaseDelta :=
    (div_pos hApos ndA5PhaseDelta_mem_Ioo.1).le
  have hqLower : (q : ℝ) ≤ A / ndA5PhaseDelta := by
    dsimp [q]
    exact Nat.floor_le hcenterNonneg
  have hqUpper : A / ndA5PhaseDelta < (q : ℝ) + 1 := by
    dsimp [q]
    simpa using Nat.lt_floor_add_one (A / ndA5PhaseDelta)
  have hqLowerMul : ndA5PhaseDelta * (q : ℝ) ≤ A := by
    simpa [mul_comm] using
      (le_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hqLower
  have hqUpperMul :
      A < ndA5PhaseDelta * ((q : ℝ) + 1) := by
    simpa [mul_comm] using
      (div_lt_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hqUpper
  have hremainderLower :
      0 ≤ A - ndA5PhaseDelta * (q : ℝ) := by
    linarith
  have hremainderUpper :
      A - ndA5PhaseDelta * (q : ℝ) < ndA5PhaseDelta := by
    nlinarith
  have hfloor :
      Int.floor (A - ndA5PhaseDelta * (q : ℝ)) = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using hremainderLower
    · simpa using hremainderUpper.trans ndA5PhaseDelta_mem_Ioo.2
  have hsweep : ndA5StrictAffineSweep A q = 1 := by
    unfold ndA5StrictAffineSweep
    rw [hfloor]
    omega
  refine ⟨q, (mem_ndA5FullTube_iff hWpos A q).mpr ?_⟩
  rw [hsweep]
  norm_num
  linarith

/-- Deterministic all-window `(t2)` packet under the source padding guard.
The proof retains the exact `alpha^3` endpoint and the lower floor estimate
for `m0`; both are load-bearing for the public ratio `13.74`. -/
theorem ndA5PaddedBandWindow_t2_of_guards
    {B j n : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hj : j < ndA5BandCount B branch)
    (hn : n ∈ ndA5PaddedBandWindow B branch C j) :
    NDA5T2ScaleFacts B n C := by
  have hlogB0 : 0 ≤ Real.log B := by linarith
  have hband := ndA5_valid_band_log_range hB branch hj
  have hnBounds := (mem_ndA5PaddedBandWindow_iff.mp hn)
  have hnLower : ndA5PaddedBandLower B branch C j ≤ (n : ℝ) :=
    (Nat.ceil_le.mp hnBounds.1)
  have hphysicalLower :
      (340 / 100000 : ℝ) * Real.log B ≤
        (n : ℝ) - (Tao.taoSection5M0 B : ℝ) := by
    have hlower := ndA5PaddedBandLower_sub_m0_lower_of_guards
      hB hlogB hpadding hj
    linarith
  have hexponents := ndA5_branchExponent_bounds branch
  have hm0le : Tao.taoSection5M0 B ≤ n := by
    have hm0cast : (Tao.taoSection5M0 B : ℝ) ≤ (n : ℝ) := by
      nlinarith [hphysicalLower]
    exact_mod_cast hm0cast
  have hnuCast :
      (((n - Tao.taoSection5M0 B : ℕ) : ℕ) : ℝ) =
        (n : ℝ) - (Tao.taoSection5M0 B : ℝ) := by
    rw [Nat.cast_sub hm0le]
  have hnuLower :
      (340 / 100000 : ℝ) * Real.log B ≤
        ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    rw [hnuCast]
    nlinarith
  have hnuPosReal : 0 < ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    nlinarith
  have hnuPos : 0 < n - Tao.taoSection5M0 B := by exact_mod_cast hnuPosReal
  have hnPos : 0 < n := by omega
  have hnUpper : (n : ℝ) ≤ ndA5PaddedBandUpper B branch C j :=
    (Nat.le_floor_iff' hnPos.ne').mp hnBounds.2
  have hm0Lower :
      (1 / 100000 : ℝ) * Real.log B - 1 <
        (Tao.taoSection5M0 B : ℝ) := by
    rw [Tao.taoSection5M0_eq_floor_log]
    have h := Nat.lt_floor_add_one (Real.log B / 100000)
    push_cast at h
    linarith
  have hnuRatioUpper :
      ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (10495 / 1000000 : ℝ) * Real.log B + 1 := by
    have hcoeff := alpha_cube_sub_one_div_ndA5LogFourThirds_lt
    unfold ndA5PaddedBandUpper at hnUpper
    have hupperScaled :
        Real.log
              (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
                (B : ℝ)) /
            ndA5LogFourThirds ≤
          (alpha ^ 3 - 1) * Real.log B / ndA5LogFourThirds := by
      exact div_le_div_of_nonneg_right
        (hband.2.trans
          (mul_le_mul_of_nonneg_right hexponents.2 hlogB0))
        ndA5LogFourThirds_pos.le
    have hcoeffScaled :
        ((alpha ^ 3 - 1) / ndA5LogFourThirds) * Real.log B ≤
          (10439 / 1000000 : ℝ) * Real.log B :=
      mul_le_mul_of_nonneg_right hcoeff.le hlogB0
    have hupperScaled' :
        Real.log
              (ndA5BandLower B branch j * Real.exp (ndA5BandBeta B branch) /
                (B : ℝ)) /
            ndA5LogFourThirds ≤
          ((alpha ^ 3 - 1) / ndA5LogFourThirds) * Real.log B := by
      calc
        _ ≤ (alpha ^ 3 - 1) * Real.log B / ndA5LogFourThirds :=
          hupperScaled
        _ = ((alpha ^ 3 - 1) / ndA5LogFourThirds) * Real.log B := by ring
    rw [hnuCast]
    norm_num at hcoeffScaled hpadding ⊢
    linarith [hupperScaled']
  have hnuUpper :
      ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (105 / 10000 : ℝ) * Real.log B := by
    norm_num at hnuRatioUpper ⊢
    linarith
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn0Lower :
      (7213 / 50000 : ℝ) * Real.log B - 1 <
        (Tao.taoSection5N0 B : ℝ) := by
    have hlogTwoUpper : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
      have h := Real.log_two_lt_d9
      norm_num at h ⊢
      exact h
    have hbase := Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
    have hcoeff :
        (7213 / 50000 : ℝ) < 1 / (10 * Real.log 2) := by
      apply (lt_div_iff₀ (mul_pos (by norm_num) hlogTwoPos)).2
      nlinarith
    have hcoeffScaled :
        (7213 / 50000 : ℝ) * Real.log B <
          (1 / (10 * Real.log 2)) * Real.log B :=
      mul_lt_mul_of_pos_right hcoeff (by linarith)
    have hbase' :
        (1 / (10 * Real.log 2)) * Real.log B - 1 <
          (Tao.taoSection5N0 B : ℝ) := by
      convert hbase using 1; ring
    linarith
  have hn0Upper :
      (Tao.taoSection5N0 B : ℝ) ≤
        (14427 / 100000 : ℝ) * Real.log B := by
    have hbase := Tao.taoSection5N0_le_log_div_ten_log_two B
    have hlogTwoLower : (693147 / 1000000 : ℝ) < Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith
    have hcoeff : 1 / (10 * Real.log 2) < (14427 / 100000 : ℝ) := by
      apply (div_lt_iff₀ (mul_pos (by norm_num) hlogTwoPos)).2
      nlinarith
    have hcoeffScaled :
        (1 / (10 * Real.log 2)) * Real.log B ≤
          (14427 / 100000 : ℝ) * Real.log B :=
      mul_le_mul_of_nonneg_right hcoeff.le hlogB0
    have hbase' :
        (Tao.taoSection5N0 B : ℝ) ≤
          (1 / (10 * Real.log 2)) * Real.log B := by
      convert hbase using 1; ring
    exact hbase'.trans hcoeffScaled
  have hratioLowerMul :
      (1374 / 100 : ℝ) *
          ((n - Tao.taoSection5M0 B : ℕ) : ℝ) ≤
        (Tao.taoSection5N0 B : ℝ) := by
    norm_num at hnuRatioUpper hn0Lower ⊢
    linarith
  have hratioUpperMul :
      (Tao.taoSection5N0 B : ℝ) ≤
        (4244 / 100 : ℝ) *
          ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
    norm_num at hn0Upper hnuLower ⊢
    linarith
  have hwidth :
      ndA5TubeWidth B C ≤
        ((n - Tao.taoSection5M0 B : ℕ) : ℝ) / 8 := by
    have hwidthMul :
        8 * ndA5TubeWidth B C ≤
          ((n - Tao.taoSection5M0 B : ℕ) : ℝ) := by
      norm_num at hpadding hnuLower ⊢
      linarith
    linarith
  exact
    { nu_pos := hnuPos
      nu_lower := hnuLower
      nu_upper := hnuUpper
      n0_div_nu_lower :=
        (le_div_iff₀ hnuPosReal).2 hratioLowerMul
      n0_div_nu_upper :=
        (div_le_iff₀ hnuPosReal).2 hratioUpperMul
      width_le_nu_div_eight := hwidth }

/-- Per-point interior-cell facts, before endpoint mass or normalization is
defined.  The source tube-constant lower guard remains visible for the later
normalizer floor. -/
structure NDA5InteriorCellFacts
    (B j nu : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : Prop where
  one_half_le_C : (1 / 2 : ℝ) ≤ C
  beta_mem : ndA5BandBeta B branch ∈ Set.Ico (1 : ℝ) 2
  m0_lt_window_lower : Tao.taoSection5M0 B <
    Nat.ceil (ndA5PaddedBandLower B branch C j)
  shifted_mem : nu + Tao.taoSection5M0 B ∈
    ndA5PaddedBandWindow B branch C j
  t2 : NDA5T2ScaleFacts B (nu + Tao.taoSection5M0 B) C
  level : NDA5PhysicalLevelFacts
    (ndA5PhysicalPhase (ndA5BandLower B branch j) M) nu

/-- Compose intrinsic containment, the all-window `(t2)` packet, and the
signed-level guard.  This theorem is pointwise in the intrinsic full tube;
nonemptiness and an unclipped left endpoint remain separate later premises. -/
theorem ndA5InteriorCellFacts_of_guards
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)) :
    NDA5InteriorCellFacts B j nu branch C M := by
  have hshifted :=
    ndA5FullTube_shift_mem_paddedBandWindow
      hB hC hlogB hM hshift hnu
  have hbeta := ndA5BandBeta_mem_Ico (Nat.zero_lt_of_lt hj)
  have hlower := ndA5M0_lt_ceil_paddedBandLower_of_guards
    hB hlogB hpadding hj
  have ht2 := ndA5PaddedBandWindow_t2_of_guards
    hB hlogB hpadding hj hshifted
  have hsub :
      nu + Tao.taoSection5M0 B - Tao.taoSection5M0 B = nu := by
    omega
  have hnuPos := ht2.nu_pos
  rw [hsub] at hnuPos
  have hWle := ht2.width_le_nu_div_eight
  rw [hsub] at hWle
  have hlevel := ndA5PhysicalLevelFacts_of_mem_fullTube hnuPos hWle hnu
  exact
    { one_half_le_C := hC
      beta_mem := hbeta
      m0_lt_window_lower := hlower
      shifted_mem := hshifted
      t2 := ht2
      level := hlevel }

/-- Global interior-cell geometry needed before the endpoint-mass carrier is
defined.  This makes the pointwise packet nonvacuous and discharges the
unclipped-left premises of the checked tube crossings/cardinality theorem. -/
structure NDA5InteriorTubeFacts
    (B j : ℕ) (branch : Tao.TaoSection5SourceBranch) (C M : ℝ) : Prop where
  nonempty : (ndA5FullTube
    (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
    (ndA5TubeWidth B C)).Nonempty
  lo_pos : 0 < ndA5TubeLo
    (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
    (ndA5TubeWidth B C)
  pointwise : ∀ nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C),
    NDA5InteriorCellFacts B j nu branch C M
  endpoint_crossings :
    ndA5StrictAffineSweep
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeLo
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C)) =
      (ndA5TubeRadius (ndA5TubeWidth B C) : ℤ) ∧
    ndA5StrictAffineSweep
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeHi
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C)) =
      -(ndA5TubeRadius (ndA5TubeWidth B C) : ℤ)
  card_error :
    |((ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C)).card : ℝ) -
        2 * ndA5TubeWidth B C / ndA5PhaseDelta| ≤
      2 + 1 / ndA5PhaseDelta

/-- Source-facing complete physical-cell packet through global tube geometry.
It deliberately stops before endpoint mass, q-support, or normalization. -/
theorem ndA5InteriorTubeFacts_of_guards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch) :
    NDA5InteriorTubeFacts B j branch C M := by
  let A := ndA5PhysicalPhase (ndA5BandLower B branch j) M
  let W := ndA5TubeWidth B C
  have hW : (71 : ℝ) ≤ W := by
    simpa [W] using ndA5TubeWidth_ge_seventy_one hC hlogB
  have hWpos : 0 < W := by linarith
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [A, W] using ndA5FullTube_nonempty_of_interior_guards
      hB hlogB hC hM hpadding hshift hj
  have hEq := ndA5FullTube_eq_Icc hWpos hne
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hloMem : ndA5TubeLo A W ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hloCell :
      NDA5InteriorCellFacts B j (ndA5TubeLo A W) branch C M := by
    apply ndA5InteriorCellFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
    simpa [A, W] using hloMem
  have hloPos : 0 < ndA5TubeLo A W := by
    have h := hloCell.t2.nu_pos
    omega
  have hpointwise : ∀ nu ∈ ndA5FullTube A W,
      NDA5InteriorCellFacts B j nu branch C M := by
    intro nu hnu
    apply ndA5InteriorCellFacts_of_guards
      hB hlogB hC hM hpadding hshift hj
    simpa [A, W] using hnu
  have hcrossings := ndA5FullTube_endpoint_crossings hWpos hne hloPos
  have hcard := ndA5FullTube_card_error hWpos hne hloPos
  exact
    { nonempty := by simpa [A, W] using hne
      lo_pos := by simpa [A, W] using hloPos
      pointwise := by simpa [A, W] using hpointwise
      endpoint_crossings := by simpa [A, W] using hcrossings
      card_error := by simpa [A, W] using hcard }

end

end ND
end Erdos1135
