/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135SecondScale.Tao.Section5.PassSchedule

/-!
# Section 5 Pass-Schedule Facts

This leaf proves the eventual arithmetic facts needed before the corrected
Proposition 5.2 event partition. In particular, every scheduled time has the
strong room `2 * m0 <= n`, so Common-Z may be used at `(m, k) = (m0, n-m0)`.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

noncomputable section

/-- The exponent of the branch source scale `y = B^beta`. -/
noncomputable def taoSection5BranchExponent :
    TaoSection5SourceBranch → ℝ
  | .alpha => taoAlpha
  | .alphaSq => taoAlpha ^ 2

theorem taoSection5SourceY_eq_branch_rpow
    (B : ℕ) (branch : TaoSection5SourceBranch) :
    taoSection5SourceY B branch =
      Real.rpow B (taoSection5BranchExponent branch) := by
  cases branch <;> rfl

/-- Linearized form of the lower endpoint of `I_y`. -/
theorem taoSection5PassLower_eq
    {B : ℕ} (hB : 1 ≤ B) (branch : TaoSection5SourceBranch) :
    taoSection5PassLower B branch =
      ((taoSection5BranchExponent branch - 1) /
          Real.log (4 / 3 : ℝ)) * Real.log B +
        Real.rpow (Real.log B) (4 / 5 : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  cases branch with
  | alpha =>
      unfold taoSection5PassLower taoSection5SourceY
        taoSection5BranchExponent
      rw [Real.log_div (Real.rpow_pos_of_pos hBpos taoAlpha).ne'
        hBpos.ne', Real.log_rpow hBpos]
      ring
  | alphaSq =>
      unfold taoSection5PassLower taoSection5SourceY
        taoSection5BranchExponent
      rw [Real.log_div
        (Real.rpow_pos_of_pos hBpos (taoAlpha ^ 2)).ne' hBpos.ne',
        Real.log_rpow hBpos]
      ring

/-- Linearized form of the upper endpoint of `I_y`. -/
theorem taoSection5PassUpper_eq
    {B : ℕ} (hB : 1 ≤ B) (branch : TaoSection5SourceBranch) :
    taoSection5PassUpper B branch =
      ((taoAlpha * taoSection5BranchExponent branch - 1) /
          Real.log (4 / 3 : ℝ)) * Real.log B -
        Real.rpow (Real.log B) (4 / 5 : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  unfold taoSection5PassUpper
  rw [taoSection5SourceY_eq_branch_rpow]
  have hYpos :
      0 < Real.rpow (B : ℝ) (taoSection5BranchExponent branch) :=
    Real.rpow_pos_of_pos hBpos _
  have hOuterPos :
      0 < Real.rpow
        (Real.rpow (B : ℝ) (taoSection5BranchExponent branch)) taoAlpha :=
    Real.rpow_pos_of_pos hYpos _
  have hlogOuter :
      Real.log (Real.rpow
          (Real.rpow (B : ℝ) (taoSection5BranchExponent branch)) taoAlpha) =
        taoAlpha * Real.log
          (Real.rpow (B : ℝ) (taoSection5BranchExponent branch)) :=
    Real.log_rpow hYpos _
  have hlogInner :
      Real.log (Real.rpow (B : ℝ) (taoSection5BranchExponent branch)) =
        taoSection5BranchExponent branch * Real.log B :=
    Real.log_rpow hBpos _
  rw [Real.log_div hOuterPos.ne' hBpos.ne', hlogOuter, hlogInner]
  ring

/-- The two branch intervals meet at one exact center before their opposite
`log(B)^0.8` buffers are applied. -/
theorem taoSection5PassUpper_alpha_add_two_slack_eq_lower_alphaSq
    {B : ℕ} (hB : 1 ≤ B) :
    taoSection5PassUpper B .alpha +
        2 * Real.rpow (Real.log B) (4 / 5 : ℝ) =
      taoSection5PassLower B .alphaSq := by
  rw [taoSection5PassUpper_eq hB .alpha,
    taoSection5PassLower_eq hB .alphaSq]
  simp only [taoSection5BranchExponent]
  ring

private theorem log_four_thirds_pos :
    0 < Real.log (4 / 3 : ℝ) :=
  Real.log_pos (by norm_num)

private theorem log_four_thirds_lt_one_third :
    Real.log (4 / 3 : ℝ) < 1 / 3 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 / 3 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

private theorem one_fourth_le_log_four_thirds :
    (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
  norm_num at h ⊢
  exact h

private theorem two_div_two_hundred_thousand_le_lower_coefficient
    (branch : TaoSection5SourceBranch) :
    (2 / 200000 : ℝ) ≤
      (taoSection5BranchExponent branch - 1) /
        Real.log (4 / 3 : ℝ) := by
  apply (le_div_iff₀ log_four_thirds_pos).2
  have hd := log_four_thirds_lt_one_third
  cases branch with
  | alpha =>
      simp only [taoSection5BranchExponent]
      norm_num [taoAlpha] at ⊢
      nlinarith
  | alphaSq =>
      simp only [taoSection5BranchExponent]
      norm_num [taoAlpha] at ⊢
      nlinarith

private theorem one_div_two_thousand_le_upper_coefficient
    (branch : TaoSection5SourceBranch) :
    (1 / 2000 : ℝ) ≤
      (taoAlpha * taoSection5BranchExponent branch - 1) /
        Real.log (4 / 3 : ℝ) := by
  apply (le_div_iff₀ log_four_thirds_pos).2
  have hd := log_four_thirds_lt_one_third
  cases branch with
  | alpha =>
      simp only [taoSection5BranchExponent]
      norm_num [taoAlpha] at ⊢
      nlinarith
  | alphaSq =>
      simp only [taoSection5BranchExponent]
      norm_num [taoAlpha] at ⊢
      nlinarith

private theorem one_div_eight_hundred_le_width_coefficient
    (branch : TaoSection5SourceBranch) :
    (1 / 800 : ℝ) ≤
      taoSection5BranchExponent branch * (taoAlpha - 1) /
        Real.log (4 / 3 : ℝ) := by
  apply (le_div_iff₀ log_four_thirds_pos).2
  have hd := log_four_thirds_lt_one_third
  cases branch with
  | alpha =>
      simp only [taoSection5BranchExponent]
      norm_num [taoAlpha] at ⊢
      nlinarith
  | alphaSq =>
      simp only [taoSection5BranchExponent]
      norm_num [taoAlpha] at ⊢
      nlinarith

private theorem upper_coefficient_lt_two_div_one_twenty_five
    (branch : TaoSection5SourceBranch) :
    (taoAlpha * taoSection5BranchExponent branch - 1) /
        Real.log (4 / 3 : ℝ) <
      (2 / 125 : ℝ) := by
  apply (div_lt_iff₀ log_four_thirds_pos).2
  have hd := one_fourth_le_log_four_thirds
  cases branch with
  | alpha =>
      simp only [taoSection5BranchExponent]
      have hnum : taoAlpha * taoAlpha - 1 < (1 / 250 : ℝ) := by
        norm_num [taoAlpha]
      nlinarith
  | alphaSq =>
      simp only [taoSection5BranchExponent]
      have hnum : taoAlpha * taoAlpha ^ 2 - 1 < (1 / 250 : ℝ) := by
        norm_num [taoAlpha]
      nlinarith

private theorem upper_sub_lower_coefficient_eq
    (branch : TaoSection5SourceBranch) :
    (taoAlpha * taoSection5BranchExponent branch - 1) /
          Real.log (4 / 3 : ℝ) -
        (taoSection5BranchExponent branch - 1) /
          Real.log (4 / 3 : ℝ) =
      taoSection5BranchExponent branch * (taoAlpha - 1) /
        Real.log (4 / 3 : ℝ) := by
  field_simp [log_four_thirds_pos.ne']
  ring

/-- The `log(B)^0.8` buffer is eventually at most `log(B)/2000`. -/
private theorem eventually_taoSection5PassSlack_le_log :
    ∀ᶠ B : ℕ in atTop,
      Real.rpow (Real.log B) (4 / 5 : ℝ) ≤
        (1 / 2000 : ℝ) * Real.log B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto
        (fun B : ℕ => (Real.log B) ^ (-(1 / 5 : ℝ)))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 5 : ℝ))).comp hlog
  filter_upwards
    [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2000),
      hlog.eventually_gt_atTop (0 : ℝ)] with B hratioB hlogB
  have hlogNonneg : 0 ≤ Real.log B := hlogB.le
  change (Real.log B) ^ (4 / 5 : ℝ) ≤
    (1 / 2000 : ℝ) * Real.log B
  calc
    (Real.log B) ^ (4 / 5 : ℝ) =
        (Real.log B) ^ (-(1 / 5 : ℝ)) *
          (Real.log B) ^ (1 : ℝ) := by
      have hadd := Real.rpow_add hlogB (-(1 / 5 : ℝ)) (1 : ℝ)
      convert hadd using 1
      norm_num
    _ = (Real.log B) ^ (-(1 / 5 : ℝ)) * Real.log B := by
      rw [Real.rpow_one]
    _ ≤ (1 / 2000 : ℝ) * Real.log B :=
      mul_le_mul_of_nonneg_right hratioB hlogNonneg

/-- Eventual common schedule data for both source branches. -/
structure TaoSection5PassScheduleFacts (B : ℕ) : Prop where
  one_le_B : 1 ≤ B
  one_le_m0 : 1 ≤ taoSection5M0 B
  lower_nonneg : ∀ branch, 0 ≤ taoSection5PassLower B branch
  upper_nonneg : ∀ branch, 0 ≤ taoSection5PassUpper B branch
  nonempty : ∀ branch, (taoSection5PassTimes B branch).Nonempty
  range : ∀ branch n, n ∈ taoSection5PassTimes B branch →
    2 * taoSection5M0 B ≤ n ∧ n ≤ taoSection5N0 B
  disjoint : Disjoint
    (taoSection5PassTimes B .alpha)
    (taoSection5PassTimes B .alphaSq)

theorem eventually_taoSection5PassScheduleFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PassScheduleFacts B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [hlog.eventually_ge_atTop (200000 : ℝ),
      eventually_taoSection5PassSlack_le_log] with B hlogLarge hslack
  have hlogPos : 0 < Real.log B := by nlinarith
  have hBReal : (1 : ℝ) < B :=
    (Real.log_pos_iff (Nat.cast_nonneg B)).1 hlogPos
  have hB : 1 ≤ B := by exact_mod_cast hBReal.le
  have hslackNonneg :
      0 ≤ Real.rpow (Real.log B) (4 / 5 : ℝ) :=
    Real.rpow_nonneg hlogPos.le _
  have hm0 : 1 ≤ taoSection5M0 B := by
    rw [taoSection5M0_eq_floor_log, Nat.one_le_floor_iff]
    nlinarith
  have hlower (branch : TaoSection5SourceBranch) :
      0 ≤ taoSection5PassLower B branch := by
    rw [taoSection5PassLower_eq hB branch]
    have hcoef := two_div_two_hundred_thousand_le_lower_coefficient branch
    have hmul := mul_le_mul_of_nonneg_right hcoef hlogPos.le
    nlinarith
  have hupper (branch : TaoSection5SourceBranch) :
      0 ≤ taoSection5PassUpper B branch := by
    rw [taoSection5PassUpper_eq hB branch]
    have hcoef := one_div_two_thousand_le_upper_coefficient branch
    have hmul := mul_le_mul_of_nonneg_right hcoef hlogPos.le
    nlinarith
  have hwidth (branch : TaoSection5SourceBranch) :
      taoSection5PassLower B branch + 2 ≤
        taoSection5PassUpper B branch := by
    rw [taoSection5PassLower_eq hB branch,
      taoSection5PassUpper_eq hB branch]
    have hcoef := one_div_eight_hundred_le_width_coefficient branch
    have hmul := mul_le_mul_of_nonneg_right hcoef hlogPos.le
    rw [← upper_sub_lower_coefficient_eq branch] at hmul
    nlinarith [hmul]
  have hnonempty (branch : TaoSection5SourceBranch) :
      (taoSection5PassTimes B branch).Nonempty := by
    have hceil :
        Nat.ceil (taoSection5PassLower B branch) ≤
          Nat.floor (taoSection5PassUpper B branch) := by
      apply Nat.le_floor
      have hceilLt := Nat.ceil_lt_add_one (hlower branch)
      nlinarith [hwidth branch]
    refine ⟨Nat.ceil (taoSection5PassLower B branch), ?_⟩
    simp [taoSection5PassTimes, hceil]
  have hrange (branch : TaoSection5SourceBranch) (n : ℕ)
      (hn : n ∈ taoSection5PassTimes B branch) :
      2 * taoSection5M0 B ≤ n ∧ n ≤ taoSection5N0 B := by
    rw [mem_taoSection5PassTimes_iff] at hn
    constructor
    · have hm0Floor :
          (taoSection5M0 B : ℝ) ≤ Real.log B / 200000 := by
        rw [taoSection5M0_eq_floor_log]
        exact Nat.floor_le (by positivity)
      have hcoef := two_div_two_hundred_thousand_le_lower_coefficient branch
      have hcoefMul := mul_le_mul_of_nonneg_right hcoef hlogPos.le
      have hlowerCast :
          (2 * taoSection5M0 B : ℝ) ≤
            taoSection5PassLower B branch := by
        rw [taoSection5PassLower_eq hB branch]
        nlinarith
      have hnCast : taoSection5PassLower B branch ≤ (n : ℝ) :=
        Nat.ceil_le.mp hn.1
      exact_mod_cast hlowerCast.trans hnCast
    · have hnCast : (n : ℝ) ≤ taoSection5PassUpper B branch :=
        (Nat.le_floor_iff (hupper branch)).mp hn.2
      have hcoef := upper_coefficient_lt_two_div_one_twenty_five branch
      have hcoefMul := mul_lt_mul_of_pos_right hcoef hlogPos
      have hupperCoarse :
          taoSection5PassUpper B branch <
            (2 / 125 : ℝ) * Real.log B := by
        rw [taoSection5PassUpper_eq hB branch]
        nlinarith
      have hlog2Pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2Lt : Real.log (2 : ℝ) < 1 := by
        have h := Real.log_lt_sub_one_of_pos
          (show (0 : ℝ) < 2 by norm_num)
          (show (2 : ℝ) ≠ 1 by norm_num)
        norm_num at h ⊢
        exact h
      have hrecip :
          (1 / 10 : ℝ) < 1 / (10 * Real.log 2) := by
        apply (lt_div_iff₀ (mul_pos (by norm_num) hlog2Pos)).2
        nlinarith
      have hrecipMul := mul_lt_mul_of_pos_right hrecip hlogPos
      have hrecipMul' :
          (1 / 10 : ℝ) * Real.log B <
            Real.log B / (10 * Real.log 2) := by
        calc
          (1 / 10 : ℝ) * Real.log B <
              (1 / (10 * Real.log 2)) * Real.log B := hrecipMul
          _ = Real.log B / (10 * Real.log 2) := by ring
      have hupperN0 :
          taoSection5PassUpper B branch <
            Real.log B / (10 * Real.log 2) - 1 := by
        calc
          taoSection5PassUpper B branch <
              (2 / 125 : ℝ) * Real.log B := hupperCoarse
          _ < (1 / 10 : ℝ) * Real.log B - 1 := by nlinarith
          _ < Real.log B / (10 * Real.log 2) - 1 := by
            nlinarith [hrecipMul']
      have hn0Lower := log_div_ten_log_two_sub_one_lt_taoSection5N0 B
      have hnLt : (n : ℝ) < (taoSection5N0 B : ℝ) :=
        hnCast.trans_lt (hupperN0.trans hn0Lower)
      exact Nat.le_of_lt (by exact_mod_cast hnLt)
  have hdisjoint : Disjoint
      (taoSection5PassTimes B .alpha)
      (taoSection5PassTimes B .alphaSq) := by
    have hslackPos :
        0 < Real.rpow (Real.log B) (4 / 5 : ℝ) :=
      Real.rpow_pos_of_pos hlogPos _
    have hsep :
        taoSection5PassUpper B .alpha <
          taoSection5PassLower B .alphaSq := by
      rw [taoSection5PassUpper_eq hB .alpha,
        taoSection5PassLower_eq hB .alphaSq]
      simp only [taoSection5BranchExponent]
      have hcenter :
          (taoAlpha * taoAlpha - 1) / Real.log (4 / 3 : ℝ) =
            (taoAlpha ^ 2 - 1) / Real.log (4 / 3 : ℝ) := by ring
      rw [hcenter]
      nlinarith [hslackPos]
    have hlowerSqPos : 0 < taoSection5PassLower B .alphaSq := by
      rw [taoSection5PassLower_eq hB .alphaSq]
      have hcoef := two_div_two_hundred_thousand_le_lower_coefficient .alphaSq
      have hmul := mul_le_mul_of_nonneg_right hcoef hlogPos.le
      nlinarith
    have hendpoint :
        Nat.floor (taoSection5PassUpper B .alpha) <
          Nat.ceil (taoSection5PassLower B .alphaSq) :=
      Nat.floor_lt_ceil_of_lt_of_pos hsep hlowerSqPos
    rw [Finset.disjoint_left]
    intro n hnAlpha hnAlphaSq
    rw [mem_taoSection5PassTimes_iff] at hnAlpha hnAlphaSq
    omega
  exact
    { one_le_B := hB
      one_le_m0 := hm0
      lower_nonneg := hlower
      upper_nonneg := hupper
      nonempty := hnonempty
      range := hrange
      disjoint := hdisjoint }

/-- The strong schedule range is exactly the Common-Z projection guard. -/
theorem TaoSection5PassScheduleFacts.m0_le_sub
    {B n : ℕ} (facts : TaoSection5PassScheduleFacts B)
    {branch : TaoSection5SourceBranch}
    (hn : n ∈ taoSection5PassTimes B branch) :
    taoSection5M0 B ≤ n - taoSection5M0 B := by
  have hroom := (facts.range branch n hn).1
  omega

theorem TaoSection5PassScheduleFacts.two_mul_m0_le
    {B n : ℕ} (facts : TaoSection5PassScheduleFacts B)
    {branch : TaoSection5SourceBranch}
    (hn : n ∈ taoSection5PassTimes B branch) :
    2 * taoSection5M0 B ≤ n :=
  (facts.range branch n hn).1

theorem TaoSection5PassScheduleFacts.m0_le
    {B n : ℕ} (facts : TaoSection5PassScheduleFacts B)
    {branch : TaoSection5SourceBranch}
    (hn : n ∈ taoSection5PassTimes B branch) :
    taoSection5M0 B ≤ n := by
  have hroom := facts.two_mul_m0_le hn
  omega

theorem TaoSection5PassScheduleFacts.sub_le_n0
    {B n : ℕ} (facts : TaoSection5PassScheduleFacts B)
    {branch : TaoSection5SourceBranch}
    (hn : n ∈ taoSection5PassTimes B branch) :
    n - taoSection5M0 B ≤ taoSection5N0 B := by
  have hn0 := (facts.range branch n hn).2
  omega

/-- Merely knowing `m0 <= n` does not imply the Common-Z guard. -/
example : 2 ≤ 3 ∧ ¬2 ≤ 3 - 2 := by decide

end

end Tao
end Erdos1135SecondScale
