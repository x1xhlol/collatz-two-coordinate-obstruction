import Erdos1135.Tao.Section5.PowerInteriorBoundaryMass
import Erdos1135.Tao.Probability.LogWindowCenteredMass

/-!
# Section 5 Passage Normalizer

This leaf compares the exact passage-time normalizer with Tao's limiting
constant.  It keeps the logarithmic source mass exact until after both the
inclusive time count and the source mass have been centered.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

noncomputable section

theorem one_fourth_le_log_four_thirds :
    (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
  norm_num at h ⊢
  exact h

theorem log_four_thirds_pos :
    0 < Real.log (4 / 3 : ℝ) :=
  Real.log_pos (by norm_num)

/-- Inclusive natural rounding changes the real interval width by at most one.
The nonnegative lower endpoint is essential because `Nat.ceil` clamps at zero.
-/
theorem abs_natCast_card_Icc_ceil_floor_sub_width_le_one
    {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hne : (Finset.Icc (Nat.ceil L) (Nat.floor U)).Nonempty) :
    |((Finset.Icc (Nat.ceil L) (Nat.floor U)).card : ℝ) - (U - L)| ≤ 1 := by
  have hbounds : Nat.ceil L ≤ Nat.floor U := Finset.nonempty_Icc.mp hne
  have hfloorLower : U - 1 < (Nat.floor U : ℝ) := Nat.sub_one_lt_floor U
  have hfloorUpper : (Nat.floor U : ℝ) ≤ U := Nat.floor_le hU
  have hceilLower : L ≤ (Nat.ceil L : ℝ) := Nat.le_ceil L
  have hceilUpper : (Nat.ceil L : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  rw [Nat.card_Icc]
  push_cast [Nat.cast_sub (show Nat.ceil L ≤ Nat.floor U + 1 by omega)]
  rw [abs_le]
  constructor <;> linarith

theorem taoSection5_log_sourceY_eq_branchExponent_mul_log
    {B : ℕ} (hB : 1 ≤ B) (branch : TaoSection5SourceBranch) :
    Real.log (taoSection5SourceY B branch) =
      taoSection5BranchExponent branch * Real.log B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rw [taoSection5SourceY_eq_branch_rpow]
  exact Real.log_rpow hBpos _

/-- Exact unrounded width of Tao's buffered first-passage interval. -/
theorem taoSection5PassUpper_sub_lower_eq
    {B : ℕ} (hB : 1 ≤ B) (branch : TaoSection5SourceBranch) :
    taoSection5PassUpper B branch - taoSection5PassLower B branch =
      ((taoAlpha - 1) * Real.log (taoSection5SourceY B branch)) /
          Real.log (4 / 3 : ℝ) -
        2 * Real.rpow (Real.log B) (4 / 5 : ℝ) := by
  rw [taoSection5PassUpper_eq hB branch,
    taoSection5PassLower_eq hB branch,
    taoSection5_log_sourceY_eq_branchExponent_mul_log hB branch]
  ring

/-- The inclusive passage-time count is centered at the unbuffered main
term, with exactly the two logarithmic buffers and one rounding unit. -/
theorem abs_taoSection5PassTimes_card_sub_main_le
    {B : ℕ} (schedule : TaoSection5PassScheduleFacts B)
    (branch : TaoSection5SourceBranch) :
    |((taoSection5PassTimes B branch).card : ℝ) -
        ((taoAlpha - 1) * Real.log (taoSection5SourceY B branch)) /
          Real.log (4 / 3 : ℝ)| ≤
      2 * Real.rpow (Real.log B) (4 / 5 : ℝ) + 1 := by
  let K : ℝ := (taoSection5PassTimes B branch).card
  let W := taoSection5PassUpper B branch - taoSection5PassLower B branch
  let M := ((taoAlpha - 1) * Real.log (taoSection5SourceY B branch)) /
    Real.log (4 / 3 : ℝ)
  let s := Real.rpow (Real.log B) (4 / 5 : ℝ)
  have hround : |K - W| ≤ 1 := by
    dsimp [K, W]
    simpa only [taoSection5PassTimes] using
      abs_natCast_card_Icc_ceil_floor_sub_width_le_one
        (schedule.lower_nonneg branch) (schedule.upper_nonneg branch)
        (by simpa only [taoSection5PassTimes] using schedule.nonempty branch)
  have hwidth : W = M - 2 * s := by
    dsimp [W, M, s]
    exact taoSection5PassUpper_sub_lower_eq schedule.one_le_B branch
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast schedule.one_le_B)) _
  have hrearrange : K - M = (K - W) + (W - M) := by ring
  rw [hrearrange]
  calc
    |(K - W) + (W - M)| ≤ |K - W| + |W - M| := abs_add_le _ _
    _ ≤ 1 + 2 * s := by
      have habs : |W - M| = 2 * s := by
        rw [hwidth, show M - 2 * s - M = -(2 * s) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg (by norm_num) hs)]
      exact add_le_add hround habs.le
    _ = 2 * s + 1 := by ring

theorem abs_taoSection5PassTimeSubtype_card_sub_main_le
    {B : ℕ} (schedule : TaoSection5PassScheduleFacts B)
    (branch : TaoSection5SourceBranch) :
    |(Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) -
        ((taoAlpha - 1) * Real.log (taoSection5SourceY B branch)) /
          Real.log (4 / 3 : ℝ)| ≤
      2 * Real.rpow (Real.log B) (4 / 5 : ℝ) + 1 := by
  simpa only [Fintype.card_coe] using
    abs_taoSection5PassTimes_card_sub_main_le schedule branch

/-- The exact odd source mass is centered at half of its logarithmic width.
-/
theorem TaoSection5PowerInteriorBoundaryMassFacts.source_mass_center
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    |logFinsetMass
          (oddLogWindow (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch)) -
        (1 / 2 : ℝ) *
          ((taoAlpha - 1) * Real.log (taoSection5SourceY B branch))| ≤
      5 / 2 := by
  have hBfour : 4 ≤ B := by
    by_contra hnot
    have hBsmall : B ≤ 3 := by omega
    have hBpos : (0 : ℝ) < B := by exact_mod_cast facts.residue.one_le_B
    have hthreePos : (0 : ℝ) < (3 : ℕ) := by norm_num
    have hlogLe : Real.log (B : ℝ) ≤ Real.log (3 : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hBpos hthreePos (by exact_mod_cast hBsmall)
    have hlogThreeLt : Real.log (3 : ℝ) < 2 := by
      have h := Real.log_lt_sub_one_of_pos
        (show (0 : ℝ) < 3 by norm_num)
        (show (3 : ℝ) ≠ 1 by norm_num)
      norm_num at h ⊢
      exact h
    nlinarith [facts.log_large, hlogLe, hlogThreeLt]
  have hBcast : (1 : ℝ) ≤ B := by exact_mod_cast facts.residue.one_le_B
  have hsourceGe : (B : ℝ) ≤ taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.self_le_rpow_of_one_le hBcast
      (one_le_taoSection5BranchExponent branch)
  have hsourceFour : (4 : ℝ) ≤ taoSection5SourceY B branch :=
    (by exact_mod_cast hBfour : (4 : ℝ) ≤ B).trans hsourceGe
  have hab :
      Nat.ceil (taoSection5SourceY B branch) ≤
        Nat.floor (Real.rpow (taoSection5SourceY B branch) taoAlpha) := by
    simpa only [taoSection5SourceLo, taoSection5SourceHi, taoNyLo, taoNyHi]
      using (show taoSection5SourceLo B branch ≤
        taoSection5SourceHi B branch by
          have h := facts.residue.width branch
          omega)
  simpa only [taoSection5SourceLo, taoSection5SourceHi, taoNyLo, taoNyHi] using
    abs_rounded_power_oddWindow_mass_sub_half_log_width_le_five_halves
      hsourceFour taoAlpha_one_lt hab

/-- The exact normalized passage count approaches `2 / log(4/3)` with an
explicit logarithmic-power error.  The denominator is not coarsened before
the centered quotient comparison. -/
theorem abs_taoSection5_passTimeRatio_sub_two_div_log_four_thirds_le
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch) :
    |(Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) /
          logFinsetMass
            (oddLogWindow (taoSection5SourceLo B branch)
              (taoSection5SourceHi B branch)) -
        2 / Real.log (4 / 3 : ℝ)| ≤
      184000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) := by
  let K : ℝ := Fintype.card {n // n ∈ taoSection5PassTimes B branch}
  let D := logFinsetMass
    (oddLogWindow (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch))
  let A := (taoAlpha - 1) * Real.log (taoSection5SourceY B branch)
  let d := Real.log (4 / 3 : ℝ)
  let L := Real.log B
  let Ly := Real.log (taoSection5SourceY B branch)
  let s := Real.rpow L (4 / 5 : ℝ)
  have hLlarge : 8000 ≤ L := by simpa only [L] using facts.log_large
  have hLpos : 0 < L := by nlinarith
  have hLone : 1 ≤ L := by nlinarith
  have hsOne : 1 ≤ s := by
    dsimp [s]
    exact Real.one_le_rpow hLone (by norm_num)
  have hsNonneg : 0 ≤ s := zero_le_one.trans hsOne
  have hLy : Ly = taoSection5BranchExponent branch * L := by
    dsimp [Ly, L]
    exact taoSection5_log_sourceY_eq_branchExponent_mul_log
      facts.residue.one_le_B branch
  have hLLy : L ≤ Ly := by
    rw [hLy]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_taoSection5BranchExponent branch) hLpos.le
  have hDLower : Ly / 8000 ≤ D := by
    simpa only [Ly, D] using facts.source_mass_lower branch
  have hDScale : L / 8000 ≤ D :=
    (div_le_div_of_nonneg_right hLLy (by norm_num)).trans hDLower
  have hDpos : 0 < D := (div_pos hLpos (by norm_num)).trans_le hDScale
  have hdPos : 0 < d := by simpa only [d] using log_four_thirds_pos
  have hdLower : (1 / 4 : ℝ) ≤ d := by
    simpa only [d] using one_fourth_le_log_four_thirds
  have htwoDiv : 2 / d ≤ 8 := by
    apply (div_le_iff₀ hdPos).2
    nlinarith [hdLower]
  have hK : |K - A / d| ≤ 3 * s := by
    have hraw := abs_taoSection5PassTimeSubtype_card_sub_main_le
      facts.geometry.schedule branch
    have hraw' : |K - A / d| ≤ 2 * s + 1 := by
      simpa only [K, A, d, s, L] using hraw
    exact hraw'.trans (by nlinarith [hsOne])
  have hmass : |A / 2 - D| ≤ 5 / 2 := by
    have hraw := facts.source_mass_center branch
    have hraw' : |D - A / 2| ≤ 5 / 2 := by
      simpa only [D, A, div_eq_mul_inv, one_mul, mul_comm] using hraw
    simpa only [abs_sub_comm] using hraw'
  have htermOne : |(K - A / d) / D| ≤ 3 * s / D := by
    rw [abs_div, abs_of_pos hDpos]
    exact div_le_div_of_nonneg_right hK hDpos.le
  have hprod : (2 / d) * |A / 2 - D| ≤ 20 := by
    calc
      (2 / d) * |A / 2 - D| ≤ 8 * |A / 2 - D| :=
        mul_le_mul_of_nonneg_right htwoDiv (abs_nonneg _)
      _ ≤ 8 * (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = 20 := by norm_num
  have htermTwo : |(2 / d) * ((A / 2 - D) / D)| ≤ 20 / D := by
    have habsCoef : |2 / d| = 2 / d := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos hdPos]
    have habsInner : |(A / 2 - D) / D| = |A / 2 - D| / D := by
      rw [abs_div, abs_of_pos hDpos]
    rw [abs_mul, habsCoef, habsInner]
    calc
      (2 / d) * (|A / 2 - D| / D) =
          ((2 / d) * |A / 2 - D|) / D := by ring
      _ ≤ 20 / D := div_le_div_of_nonneg_right hprod hDpos.le
  have hrearrange :
      K / D - 2 / d =
        (K - A / d) / D + (2 / d) * ((A / 2 - D) / D) := by
    field_simp [hDpos.ne', hdPos.ne']
    ring
  have hInv : 1 / D ≤ 8000 / L := by
    apply (div_le_div_iff₀ hDpos hLpos).2
    nlinarith [hDScale]
  rw [hrearrange]
  calc
    |(K - A / d) / D + (2 / d) * ((A / 2 - D) / D)| ≤
        |(K - A / d) / D| + |(2 / d) * ((A / 2 - D) / D)| :=
      abs_add_le _ _
    _ ≤ 3 * s / D + 20 / D := add_le_add htermOne htermTwo
    _ = (3 * s + 20) / D := by ring
    _ ≤ 23 * s / D := by
      exact div_le_div_of_nonneg_right (by nlinarith [hsOne]) hDpos.le
    _ = 23 * s * (1 / D) := by ring
    _ ≤ 23 * s * (8000 / L) :=
      mul_le_mul_of_nonneg_left hInv (mul_nonneg (by norm_num) hsNonneg)
    _ = 184000 * (s / L) := by ring
    _ = 184000 * Real.rpow L (-1 / 5 : ℝ) := by
      congr 1
      calc
        s / L = Real.rpow L (4 / 5 : ℝ) / L := by rfl
        _ = Real.rpow L ((4 / 5 : ℝ) - 1) := by
          have hsub := Real.rpow_sub hLpos (4 / 5 : ℝ) 1
          rw [Real.rpow_one] at hsub
          exact hsub.symm
        _ = Real.rpow L (-1 / 5 : ℝ) := by norm_num

theorem eventually_abs_taoSection5_passTimeRatio_sub_two_div_log_four_thirds_le :
    ∀ᶠ B : ℕ in atTop,
      ∀ branch : TaoSection5SourceBranch,
        |(Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) /
              logFinsetMass
                (oddLogWindow (taoSection5SourceLo B branch)
                  (taoSection5SourceHi B branch)) -
            2 / Real.log (4 / 3 : ℝ)| ≤
          184000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) := by
  filter_upwards [eventually_taoSection5PowerInteriorBoundaryMassFacts]
    with B facts
  exact abs_taoSection5_passTimeRatio_sub_two_div_log_four_thirds_le facts

/-- Once the explicit normalizer error is at most one, the exact passage
normalizer has a branch-uniform constant upper bound. -/
theorem taoSection5_passTimeRatio_le_nine_of_normalizer_error_le_one
    {B : ℕ} (facts : TaoSection5PowerInteriorBoundaryMassFacts B)
    (branch : TaoSection5SourceBranch)
    (hsmall :
      184000 * Real.rpow (Real.log B) (-1 / 5 : ℝ) ≤ 1) :
    (Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) /
        logFinsetMass
          (oddLogWindow (taoSection5SourceLo B branch)
            (taoSection5SourceHi B branch)) ≤
      9 := by
  have hnorm :=
    abs_taoSection5_passTimeRatio_sub_two_div_log_four_thirds_le facts branch
  have hmain : 2 / Real.log (4 / 3 : ℝ) ≤ 8 := by
    apply (div_le_iff₀ log_four_thirds_pos).2
    nlinarith [one_fourth_le_log_four_thirds]
  have hupper := (abs_le.mp hnorm).2
  nlinarith

theorem eventually_taoSection5_passTimeRatio_le_nine :
    ∀ᶠ B : ℕ in atTop,
      ∀ branch : TaoSection5SourceBranch,
        (Fintype.card {n // n ∈ taoSection5PassTimes B branch} : ℝ) /
            logFinsetMass
              (oddLogWindow (taoSection5SourceLo B branch)
                (taoSection5SourceHi B branch)) ≤
          9 := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-1 / 5 : ℝ))
        atTop (nhds 0) := by
    simpa only [show (-1 / 5 : ℝ) = -(1 / 5 : ℝ) by norm_num] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 5 : ℝ))).comp hlog
  filter_upwards
    [eventually_taoSection5PowerInteriorBoundaryMassFacts,
      hdecay.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 184000)]
      with B facts hsmall
  intro branch
  apply taoSection5_passTimeRatio_le_nine_of_normalizer_error_le_one
    facts branch
  nlinarith

end

end Tao
end Erdos1135
