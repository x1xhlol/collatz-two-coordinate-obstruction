/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Band.A5PhysicalPaddingRate

/-!
# A5 Padded-Band Diameter

This leaf proves the H3 separation input for the original padded `J_j`
carrier.  It does not replace `J_j` by Tao's trimmed pass-time schedule.
The ordered formulation avoids any extra endpoint-rounding loss.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private theorem one_fourth_le_ndA5LogFourThirds :
    (1 / 4 : ℝ) ≤ ndA5LogFourThirds := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
  unfold ndA5LogFourThirds
  norm_num at h ⊢
  exact h

private theorem ndA5PaddedBandUpper_sub_lower
    {B j : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) :
    ndA5PaddedBandUpper B branch C j -
        ndA5PaddedBandLower B branch C j =
      ndA5BandBeta B branch / ndA5LogFourThirds +
        6 * ndA5TubeWidth B C := by
  unfold ndA5PaddedBandUpper ndA5PaddedBandLower
  rw [ndA5_log_bandUpper_div hB branch,
    ndA5_log_bandLower_div hB branch]
  ring

/-- Eventually, every time in an original padded A5 window lies strictly
after the common step-back time.  This companion to H3 prevents truncated
subtraction in the finite terminal-atom index. -/
theorem eventually_ndA5M0_lt_of_mem_paddedBandWindow
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
        j < ndA5BandCount B branch →
          ∀ n ∈ ndA5PaddedBandWindow B branch C j,
            Tao.taoSection5M0 B < n := by
  have hCpos : 0 < C := by positivity
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_three_mul_ndA5TubeWidth_le_log C hCpos,
      hlog.eventually_ge_atTop (300000 : ℝ),
      eventually_ge_atTop 1] with B hpadding hlogB hB
  intro branch j hj n hn
  have hm0Ceil := ndA5M0_lt_ceil_paddedBandLower_of_guards
    hB hlogB hpadding hj
  exact hm0Ceil.trans_le (mem_ndA5PaddedBandWindow_iff.mp hn).1

/-- Eventually, any two ordered times in one original padded A5 window are
separated by at most the common step-back time.  This is the H3 input used
later to prove disjointness of unrestricted terminal atoms. -/
theorem eventually_ndA5PaddedBandWindow_diameter_le_m0
    (C : ℝ) (hC : (1 / 2 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch) (j : ℕ),
        j < ndA5BandCount B branch →
          ∀ n ∈ ndA5PaddedBandWindow B branch C j,
            ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
              n ≤ n' → n' - n ≤ Tao.taoSection5M0 B := by
  have hscaledC : 0 < (132 : ℝ) * C := by positivity
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_three_mul_ndA5TubeWidth_le_log
      ((132 : ℝ) * C) hscaledC,
      hlog.eventually_ge_atTop (2000000 : ℝ),
      eventually_ge_atTop 1] with B hscaled hlogB hB
  have hWnonneg : 0 ≤ ndA5TubeWidth B C := by
    unfold ndA5TubeWidth
    positivity
  have hscale :
      ndA5TubeWidth B ((132 : ℝ) * C) =
        132 * ndA5TubeWidth B C := by
    unfold ndA5TubeWidth
    ring
  rw [hscale] at hscaled
  have hSixWidth :
      6 * ndA5TubeWidth B C ≤
        (1 / 1000000 : ℝ) * Real.log B := by
    nlinarith
  have hpadding :
      3 * ndA5TubeWidth B C ≤
        (33 / 500000 : ℝ) * Real.log B := by
    nlinarith
  have hlogGuard : (300000 : ℝ) ≤ Real.log B := by linarith
  have hm0Lower :
      Real.log B / 200000 ≤ (Tao.taoSection5M0 B : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (Real.log B / 100000)
    rw [← Tao.taoSection5M0_eq_floor_log B] at hfloor

    nlinarith
  intro branch j hj n hn n' hn' hnn'
  have hcount : 0 < ndA5BandCount B branch := Nat.zero_lt_of_lt hj
  have hbeta := ndA5BandBeta_mem_Ico hcount
  have hbetaDiv :
      ndA5BandBeta B branch / ndA5LogFourThirds < 8 := by
    apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
    nlinarith [one_fourth_le_ndA5LogFourThirds, hbeta.2]
  have hwidth :
      ndA5PaddedBandUpper B branch C j -
          ndA5PaddedBandLower B branch C j <
        Real.log B / 200000 := by
    rw [ndA5PaddedBandUpper_sub_lower hB branch C]
    nlinarith
  have hm0Ceil :
      Tao.taoSection5M0 B <
        Nat.ceil (ndA5PaddedBandLower B branch C j) :=
    ndA5M0_lt_ceil_paddedBandLower_of_guards
      hB hlogGuard hpadding hj
  have hnBounds := mem_ndA5PaddedBandWindow_iff.mp hn
  have hn'Bounds := mem_ndA5PaddedBandWindow_iff.mp hn'
  have hnPos : 0 < n := by omega
  have hn'Pos : 0 < n' := hnPos.trans_le hnn'
  have hnLower :
      ndA5PaddedBandLower B branch C j ≤ (n : ℝ) :=
    Nat.ceil_le.mp hnBounds.1
  have hn'Upper :
      (n' : ℝ) ≤ ndA5PaddedBandUpper B branch C j :=
    (Nat.le_floor_iff' hn'Pos.ne').mp hn'Bounds.2
  have hsubCast :
      ((n' - n : ℕ) : ℝ) = (n' : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hnn']
  have hsubReal : ((n' - n : ℕ) : ℝ) < Real.log B / 200000 := by
    rw [hsubCast]
    linarith
  exact_mod_cast hsubReal.le.trans hm0Lower

end

end ND
end Erdos1135
