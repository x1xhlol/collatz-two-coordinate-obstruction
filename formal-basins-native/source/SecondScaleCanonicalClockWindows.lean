import SecondScaleSyracuseCenteredPassage
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao Filter
open scoped Topology

theorem canonical_window_threshold_le {B q : ℕ} (hB : 0 < B)
    {branch : TaoSection5SourceBranch}
    (hq : q ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    B ≤ q := by
  have hlo : taoSection5SourceLo B branch ≤ q := by
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  exact (taoSection5Threshold_le_sourceLo hB branch).trans hlo

theorem canonical_window_threshold_lt {B q : ℕ} (hB : 1 < B)
    {branch : TaoSection5SourceBranch}
    (hq : q ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    B < q := by
  have hlo : taoSection5SourceLo B branch ≤ q :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hexp : 1 < taoSection5BranchExponent branch := by
    cases branch <;> norm_num [taoSection5BranchExponent, taoAlpha]
  have hreal : (B : ℝ) < taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.self_lt_rpow_of_one_lt (by exact_mod_cast hB) hexp
  have hceil : taoSection5SourceY B branch ≤ (taoSection5SourceLo B branch : ℝ) :=
    Nat.le_ceil _
  have hcast : (taoSection5SourceLo B branch : ℝ) ≤ q := by exact_mod_cast hlo
  exact_mod_cast hreal.trans_le (hceil.trans hcast)

theorem canonical_clock_cost {B : ℕ} (hB : 0 < B) :
    (taoSection5N0 B : ℝ) / (3 * B) ≤ 1 := by
  have hn : taoSection5N0 B ≤ B := by
    exact (Nat.div_le_self _ _).trans (Nat.log_le_self _ _)
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  apply (div_le_one (by positivity)).mpr
  have hn' : (taoSection5N0 B : ℝ) ≤ B := by exact_mod_cast hn
  linarith

theorem canonical_clock_center_bound {B q : ℕ} (hB : 0 < B)
    {branch : TaoSection5SourceBranch}
    (hq : q ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    clockCenter B q ≤ (2 / 125 : ℝ) * Real.log B := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hq' : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le hB (canonical_window_threshold_le hB hq)
  have hhi : q ≤ taoSection5SourceHi B branch := by
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
  have hypos : 0 < taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hB' _
  have hqr : (q : ℝ) ≤ (taoSection5SourceY B branch) ^ taoAlpha := by
    have hh : (q : ℝ) ≤ taoSection5SourceHi B branch := by exact_mod_cast hhi
    exact hh.trans (Nat.floor_le (Real.rpow_pos_of_pos hypos taoAlpha).le)
  have hlogs := Real.log_le_log hq' hqr
  rw [Real.log_rpow hypos, taoSection5SourceY_eq_branch_rpow] at hlogs
  have hlogpow : Real.log (Real.rpow (B : ℝ) (taoSection5BranchExponent branch)) =
      taoSection5BranchExponent branch * Real.log B := Real.log_rpow hB' _
  rw [hlogpow] at hlogs
  have hcoef : taoAlpha * taoSection5BranchExponent branch - 1 ≤ (1 / 250 : ℝ) := by
    cases branch <;> norm_num [taoSection5BranchExponent, taoAlpha]
  have hnum : Real.log (q : ℝ) - Real.log B ≤ (1 / 250 : ℝ) * Real.log B := by
    have hm := mul_le_mul_of_nonneg_right hcoef hlog
    nlinarith
  unfold clockCenter
  apply (div_le_iff₀ clockDrift_pos).mpr
  have hm := mul_le_mul_of_nonneg_left clockDrift_ge_quarter hlog
  nlinarith

theorem canonical_clock_upperIndex_le {B q : ℕ} {E : ℝ}
    (hB : 0 < B) (hlog : 100 ≤ Real.log (B : ℝ)) (hE : 0 ≤ E)
    (hEmax : E ≤ Real.log (B : ℝ) / 1000)
    {branch : TaoSection5SourceBranch}
    (hq : q ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    clockUpperIndex B q E ≤ taoSection5N0 B := by
  have hcenter := canonical_clock_center_bound hB hq
  have hradius := clockRadius_le_five hE
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogtwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn := log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hdiv : Real.log (B : ℝ) / 10 ≤ Real.log (B : ℝ) / (10 * Real.log 2) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    linarith
  unfold clockUpperIndex
  apply Nat.ceil_le.mpr
  unfold clockRadius at hradius
  linarith

theorem eventually_typicalSlack_le_log :
    ∀ᶠ B : ℕ in atTop, taoSection5TypicalSlack B ≤ Real.log B / 1000 := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun B : ℕ => (Real.log B) ^ (-(2 / 5 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 / 5 : ℝ))).comp hlog
  filter_upwards
    [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 1000),
      hlog.eventually_gt_atTop (0 : ℝ)] with B hratioB hlogB
  have hpower : taoSection5TypicalSlack B =
      (Real.log B) ^ (-(2 / 5 : ℝ)) * Real.log B := by
    unfold taoSection5TypicalSlack
    have hadd := Real.rpow_add hlogB (-(2 / 5 : ℝ)) (1 : ℝ)
    norm_num at hadd
    exact hadd
  calc
    taoSection5TypicalSlack B =
        (Real.log B) ^ (-(2 / 5 : ℝ)) * Real.log B := hpower
    _ ≤ (1 / 1000 : ℝ) * Real.log B :=
      mul_le_mul_of_nonneg_right hratioB hlogB.le
    _ = Real.log B / 1000 := by ring

theorem eventually_canonical_clock_windows :
    ∀ᶠ B : ℕ in atTop, 1 < B ∧
      (taoSection5N0 B : ℝ) / (3 * B) ≤ 1 ∧
      ∀ (branch : TaoSection5SourceBranch) (q : ℕ),
        q ∈ oddLogWindow (taoSection5SourceLo B branch) (taoSection5SourceHi B branch) →
        B < q ∧ clockUpperIndex B q (taoSection5TypicalSlack B) ≤ taoSection5N0 B := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog.eventually_ge_atTop (100 : ℝ),
      eventually_typicalSlack_le_log] with B hB hlogB hslack
  have hBpos : 0 < B := lt_trans Nat.zero_lt_one hB
  refine ⟨hB, canonical_clock_cost hBpos, ?_⟩
  intro branch q hq
  refine ⟨canonical_window_threshold_lt hB hq,
    canonical_clock_upperIndex_le hBpos hlogB ?_ hslack hq⟩
  exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hB.le)) _

end CollatzClockSecondScale
