/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135.Tao.Section5.PassScheduleFacts

/-!
# Section 5 Repaired Power-Interior Facts

This leaf proves the deterministic geometry of the repaired source interior
`[y^(1+delta), y^(alpha-delta)]`. It establishes rounding-safe odd
nonemptiness and inclusion in the original branch source window. Logarithmic
mass loss and trajectory localization remain separate probability consumers.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

noncomputable section

theorem one_le_taoSection5BranchExponent
    (branch : TaoSection5SourceBranch) :
    1 ≤ taoSection5BranchExponent branch := by
  cases branch <;> norm_num [taoSection5BranchExponent, taoAlpha]

private theorem eventually_taoSection5PowerInteriorDelta_lt :
    ∀ᶠ B : ℕ in atTop,
      taoSection5PowerInteriorDelta B < (1 / 8000 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdelta :
      Tendsto
        (fun B : ℕ => (Real.log B) ^ (-(1 / 10 : ℝ)))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp hlog
  filter_upwards
    [hdelta.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8000)]
    with B hB
  unfold taoSection5PowerInteriorDelta
  simpa only [show (-(1 / 10 : ℝ)) = (-1 / 10 : ℝ) by norm_num]
    using hB

private theorem eventually_three_le_threshold_rpow_one_div_four_thousand :
    ∀ᶠ B : ℕ in atTop,
      (3 : ℝ) ≤ (B : ℝ) ^ (1 / 4000 : ℝ) := by
  have htendsto :
      Tendsto (fun B : ℕ => (B : ℝ) ^ (1 / 4000 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 4000 : ℝ))).comp
        tendsto_natCast_atTop_atTop
  exact htendsto.eventually_ge_atTop 3

/-- Eventual deterministic geometry of the repaired branch interiors. -/
structure TaoSection5PowerInteriorFacts (B : ℕ) : Prop where
  schedule : TaoSection5PassScheduleFacts B
  delta_pos : 0 < taoSection5PowerInteriorDelta B
  delta_lt : taoSection5PowerInteriorDelta B < (1 / 8000 : ℝ)
  source_le_lower : ∀ branch,
    taoSection5SourceY B branch ≤
      taoSection5PowerInteriorLower B branch
  upper_le_source : ∀ branch,
    taoSection5PowerInteriorUpper B branch ≤
      Real.rpow (taoSection5SourceY B branch) taoAlpha
  width : ∀ branch,
    taoSection5PowerInteriorLower B branch + 2 ≤
      taoSection5PowerInteriorUpper B branch
  endpoint_room : ∀ branch,
    Nat.ceil (taoSection5PowerInteriorLower B branch) + 1 ≤
      Nat.floor (taoSection5PowerInteriorUpper B branch)
  nonempty : ∀ branch,
    (taoSection5PowerInterior B branch).Nonempty
  mass_pos : ∀ branch,
    0 < logFinsetMass (taoSection5PowerInterior B branch)
  subset_source : ∀ branch,
    taoSection5PowerInterior B branch ⊆
      oddLogWindow (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch)

theorem eventually_taoSection5PowerInteriorFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PowerInteriorFacts B := by
  filter_upwards
    [eventually_taoSection5PassScheduleFacts,
      eventually_taoSection5PowerInteriorDelta_lt,
      eventually_three_le_threshold_rpow_one_div_four_thousand]
    with B schedule hdeltaSmall hBgrowth
  have hBne : B ≠ 1 := by
    intro hB
    subst B
    norm_num at hBgrowth
  have hBgt : 1 < B := lt_of_le_of_ne schedule.one_le_B hBne.symm
  have hBcast : (1 : ℝ) ≤ B := by exact_mod_cast hBgt.le
  have hBpos : (0 : ℝ) < B := zero_lt_one.trans_le hBcast
  have hlogPos : 0 < Real.log B := Real.log_pos (by exact_mod_cast hBgt)
  have hdeltaPos : 0 < taoSection5PowerInteriorDelta B := by
    unfold taoSection5PowerInteriorDelta
    exact Real.rpow_pos_of_pos hlogPos _
  have hgap :
      (1 / 4000 : ℝ) <
        taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B := by
    have halpha : taoAlpha - 1 = (1 / 2000 : ℝ) := by
      norm_num [taoAlpha]
    rw [halpha]
    nlinarith
  have hsourceOne (branch : TaoSection5SourceBranch) :
      1 ≤ taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.one_le_rpow hBcast
      (zero_le_one.trans (one_le_taoSection5BranchExponent branch))
  have hsourcePos (branch : TaoSection5SourceBranch) :
      0 < taoSection5SourceY B branch :=
    zero_lt_one.trans_le (hsourceOne branch)
  have hsourceGe (branch : TaoSection5SourceBranch) :
      (B : ℝ) ≤ taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.self_le_rpow_of_one_le hBcast
      (one_le_taoSection5BranchExponent branch)
  have hlowerOne (branch : TaoSection5SourceBranch) :
      1 ≤ taoSection5PowerInteriorLower B branch := by
    unfold taoSection5PowerInteriorLower
    exact Real.one_le_rpow (hsourceOne branch) (by linarith)
  have hlowerNonneg (branch : TaoSection5SourceBranch) :
      0 ≤ taoSection5PowerInteriorLower B branch :=
    zero_le_one.trans (hlowerOne branch)
  have hsourceLower (branch : TaoSection5SourceBranch) :
      taoSection5SourceY B branch ≤
        taoSection5PowerInteriorLower B branch := by
    unfold taoSection5PowerInteriorLower
    exact Real.self_le_rpow_of_one_le (hsourceOne branch) (by linarith)
  have hupperSource (branch : TaoSection5SourceBranch) :
      taoSection5PowerInteriorUpper B branch ≤
        Real.rpow (taoSection5SourceY B branch) taoAlpha := by
    unfold taoSection5PowerInteriorUpper
    exact Real.rpow_le_rpow_of_exponent_le (hsourceOne branch) (by linarith)
  have hfactor (branch : TaoSection5SourceBranch) :
      (3 : ℝ) ≤ Real.rpow (taoSection5SourceY B branch)
        (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B) := by
    have hBExponent :
        (B : ℝ) ^ (1 / 4000 : ℝ) ≤
          (B : ℝ) ^
            (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B) :=
      Real.rpow_le_rpow_of_exponent_le hBcast hgap.le
    have hbase :
        (B : ℝ) ^
            (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B) ≤
          (taoSection5SourceY B branch) ^
            (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B) :=
      Real.rpow_le_rpow (Nat.cast_nonneg B) (hsourceGe branch)
        ((by norm_num : (0 : ℝ) ≤ 1 / 4000).trans hgap.le)
    exact hBgrowth.trans (hBExponent.trans hbase)
  have hfactorization (branch : TaoSection5SourceBranch) :
      taoSection5PowerInteriorUpper B branch =
        taoSection5PowerInteriorLower B branch *
          Real.rpow (taoSection5SourceY B branch)
            (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B) := by
    unfold taoSection5PowerInteriorUpper taoSection5PowerInteriorLower
    have hadd := Real.rpow_add (hsourcePos branch)
      (1 + taoSection5PowerInteriorDelta B)
      (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B)
    calc
      Real.rpow (taoSection5SourceY B branch)
          (taoAlpha - taoSection5PowerInteriorDelta B) =
          Real.rpow (taoSection5SourceY B branch)
            ((1 + taoSection5PowerInteriorDelta B) +
              (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B)) := by
        congr 2
        ring
      _ = Real.rpow (taoSection5SourceY B branch)
            (1 + taoSection5PowerInteriorDelta B) *
          Real.rpow (taoSection5SourceY B branch)
            (taoAlpha - 1 - 2 * taoSection5PowerInteriorDelta B) := hadd
  have hwidth (branch : TaoSection5SourceBranch) :
      taoSection5PowerInteriorLower B branch + 2 ≤
        taoSection5PowerInteriorUpper B branch := by
    have hmul := mul_le_mul_of_nonneg_left (hfactor branch)
      (hlowerNonneg branch)
    have hthree :
        taoSection5PowerInteriorLower B branch + 2 ≤
          taoSection5PowerInteriorLower B branch * 3 := by
      nlinarith [hlowerOne branch]
    rw [hfactorization branch]
    exact hthree.trans hmul
  have hroom (branch : TaoSection5SourceBranch) :
      Nat.ceil (taoSection5PowerInteriorLower B branch) + 1 ≤
        Nat.floor (taoSection5PowerInteriorUpper B branch) := by
    have hnonempty := oddLogWindow_ceil_floor_nonempty_of_add_two_le
      (hlowerNonneg branch) (hwidth branch)
    have hceil := Nat.ceil_lt_add_one (hlowerNonneg branch)
    apply Nat.le_floor
    norm_num at hceil ⊢
    linarith [hwidth branch]
  have hnonempty (branch : TaoSection5SourceBranch) :
      (taoSection5PowerInterior B branch).Nonempty := by
    unfold taoSection5PowerInterior
    exact oddLogWindow_nonempty_of_succ_le (hroom branch)
  have hmass (branch : TaoSection5SourceBranch) :
      0 < logFinsetMass (taoSection5PowerInterior B branch) := by
    unfold taoSection5PowerInterior
    exact logFinsetMass_oddLogWindow_pos_of_succ_le (hroom branch)
  have hsubset (branch : TaoSection5SourceBranch) :
      taoSection5PowerInterior B branch ⊆
        oddLogWindow (taoSection5SourceLo B branch)
          (taoSection5SourceHi B branch) := by
    unfold taoSection5PowerInterior taoSection5SourceLo
      taoSection5SourceHi taoNyLo taoNyHi
    apply oddLogWindow_mono
    · exact Nat.ceil_le_ceil (hsourceLower branch)
    · exact Nat.floor_mono (hupperSource branch)
  exact
    { schedule := schedule
      delta_pos := hdeltaPos
      delta_lt := hdeltaSmall
      source_le_lower := hsourceLower
      upper_le_source := hupperSource
      width := hwidth
      endpoint_room := hroom
      nonempty := hnonempty
      mass_pos := hmass
      subset_source := hsubset }

end

end Tao
end Erdos1135
