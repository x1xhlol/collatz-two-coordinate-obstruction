/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.LogSupportPerturbation
import Erdos1135SecondScale.Tao.Probability.LogWindowEndpoints
import Erdos1135SecondScale.Tao.Probability.ReciprocalProgression

/-!
# Floor Perturbations Of Tao Logarithmic Windows

This neutral proof leaf compares two ordered odd logarithmic windows.  It keeps
the first reciprocal endpoint in the shell estimate, so later real-to-natural
window adapters can retain a polynomial error rate.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

noncomputable section

/-- On positive naturals, the shifted project-local logarithmic weight is the
ordinary reciprocal weight. -/
theorem logNatWeight_eq_one_div_of_pos {n : ℕ} (hn : 0 < n) :
    logNatWeight n = 1 / (n : ℝ) := by
  rcases n with _ | n
  · omega
  simp [logNatWeight, logWeight]

/-- Dropping the oddness filter can only increase logarithmic mass. -/
theorem logFinsetMass_oddLogWindow_le_sum_Icc_reciprocal
    {A U : ℕ} (hA : 1 ≤ A) :
    logFinsetMass (oddLogWindow A U) ≤
      ∑ N ∈ Finset.Icc A U, 1 / (N : ℝ) := by
  classical
  unfold logFinsetMass
  calc
    (∑ N ∈ oddLogWindow A U, logNatWeight N) =
        ∑ N ∈ oddLogWindow A U, 1 / (N : ℝ) := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [logNatWeight_eq_one_div_of_pos]
      have hAN := (oddLogWindow_mem.mp hN).1
      omega
    _ ≤ ∑ N ∈ Finset.Icc A U, 1 / (N : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro N hN
        exact Finset.mem_Icc.mpr ⟨(oddLogWindow_mem.mp hN).1,
          (oddLogWindow_mem.mp hN).2.1⟩
      · intro N _hN _hnot
        positivity

/-- For ordered endpoints, values lost from the first window lie in its lower
endpoint shell. -/
theorem oddLogWindow_sdiff_subset_lowerShell
    {lo₀ hi₀ lo₁ hi₁ : ℕ} (hhi : hi₀ ≤ hi₁) :
    oddLogWindow lo₀ hi₀ \ oddLogWindow lo₁ hi₁ ⊆
      oddLogWindow lo₀ (lo₁ - 1) := by
  intro N hN
  rw [Finset.mem_sdiff] at hN
  rw [oddLogWindow_mem] at hN ⊢
  rcases hN with ⟨⟨hlo₀N, hNhi₀, hodd⟩, hnot⟩
  have hnot' : ¬ (lo₁ ≤ N ∧ N ≤ hi₁ ∧ N % 2 = 1) := by
    simpa only [oddLogWindow_mem] using hnot
  exact ⟨hlo₀N, by omega, hodd⟩

/-- For ordered endpoints, values gained by the second window lie in its upper
endpoint shell. -/
theorem oddLogWindow_sdiff_subset_upperShell
    {lo₀ hi₀ lo₁ hi₁ : ℕ} (hlo : lo₀ ≤ lo₁) :
    oddLogWindow lo₁ hi₁ \ oddLogWindow lo₀ hi₀ ⊆
      oddLogWindow (hi₀ + 1) hi₁ := by
  intro N hN
  rw [Finset.mem_sdiff] at hN
  rw [oddLogWindow_mem] at hN ⊢
  rcases hN with ⟨⟨hlo₁N, hNhi₁, hodd⟩, hnot⟩
  have hnot' : ¬ (lo₀ ≤ N ∧ N ≤ hi₀ ∧ N % 2 = 1) := by
    simpa only [oddLogWindow_mem] using hnot
  exact ⟨by omega, hNhi₁, hodd⟩

/-- Ordered endpoint movement is controlled by the two endpoint shells. -/
theorem logFinsetSymmDiffMass_oddLogWindow_le_shells
    {lo₀ hi₀ lo₁ hi₁ : ℕ} (hlo : lo₀ ≤ lo₁) (hhi : hi₀ ≤ hi₁) :
    logFinsetSymmDiffMass (oddLogWindow lo₀ hi₀) (oddLogWindow lo₁ hi₁) ≤
      logFinsetMass (oddLogWindow lo₀ (lo₁ - 1)) +
        logFinsetMass (oddLogWindow (hi₀ + 1) hi₁) := by
  unfold logFinsetSymmDiffMass
  exact add_le_add
    (logFinsetMass_mono (oddLogWindow_sdiff_subset_lowerShell hhi))
    (logFinsetMass_mono (oddLogWindow_sdiff_subset_upperShell hlo))

/-- A reciprocal endpoint shell produced by moving a base from `B` to a real
`x < B + 1` has mass at most `3 / B`, uniformly for exponents in `[1, 2]`.
The assumptions on `A` and `U` deliberately expose the two rounding facts
needed by lower and upper endpoint shells. -/
theorem logFinsetMass_oddLogWindow_le_three_div_of_floor_shell
    {B A U : ℕ} {x gamma : ℝ}
    (hB : 1 ≤ B) (hBx : (B : ℝ) ≤ x) (hxB : x ≤ (B : ℝ) + 1)
    (hgammaOne : 1 ≤ gamma) (hgammaTwo : gamma ≤ 2)
    (hBA : (B : ℝ) ^ gamma ≤ (A : ℝ))
    (hUx : (U : ℝ) ≤ x ^ gamma) :
    logFinsetMass (oddLogWindow A U) ≤ 3 / (B : ℝ) := by
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hBone : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hxpos : 0 < x := hBpos.trans_le hBx
  have hgammaNonneg : 0 ≤ gamma := by linarith
  have hBself : (B : ℝ) ≤ (B : ℝ) ^ gamma :=
    Real.self_le_rpow_of_one_le hBone hgammaOne
  have hBAcast : (B : ℝ) ≤ (A : ℝ) := hBself.trans hBA
  have hBA_nat : B ≤ A := by exact_mod_cast hBAcast
  have hA : 1 ≤ A := hB.trans hBA_nat
  by_cases hAU : A ≤ U
  · have hApos : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
    have hUpos : 0 < (U : ℝ) := by
      exact hApos.trans_le (by exact_mod_cast hAU)
    have hBpowPos : 0 < (B : ℝ) ^ gamma :=
      Real.rpow_pos_of_pos hBpos gamma
    have hxpowPos : 0 < x ^ gamma := Real.rpow_pos_of_pos hxpos gamma
    have hlogU : Real.log (U : ℝ) ≤ Real.log (x ^ gamma) :=
      Real.strictMonoOn_log.monotoneOn hUpos hxpowPos hUx
    have hlogB : Real.log ((B : ℝ) ^ gamma) ≤ Real.log (A : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hBpowPos hApos hBA
    have hlogGap : Real.log x - Real.log (B : ℝ) ≤ 1 / (B : ℝ) := by
      have hratioPos : 0 < x / (B : ℝ) := div_pos hxpos hBpos
      have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
      have hratio : x / (B : ℝ) - 1 ≤ 1 / (B : ℝ) := by
        apply (sub_le_iff_le_add).2
        calc
          x / (B : ℝ) ≤ ((B : ℝ) + 1) / (B : ℝ) := by
            exact div_le_div_of_nonneg_right hxB hBpos.le
          _ = 1 / (B : ℝ) + 1 := by
            field_simp
            ring
      rw [Real.log_div hxpos.ne' hBpos.ne'] at hlogRatio
      exact hlogRatio.trans hratio
    have hgammaLog :
        gamma * (Real.log x - Real.log (B : ℝ)) ≤ 2 / (B : ℝ) := by
      calc
        gamma * (Real.log x - Real.log (B : ℝ)) ≤
            gamma * (1 / (B : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogGap hgammaNonneg
        _ ≤ 2 * (1 / (B : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hgammaTwo (one_div_nonneg.mpr hBpos.le)
        _ = 2 / (B : ℝ) := by ring
    have hlogShell :
        Real.log ((U : ℝ) / (A : ℝ)) ≤ 2 / (B : ℝ) := by
      rw [Real.log_rpow hxpos] at hlogU
      rw [Real.log_rpow hBpos] at hlogB
      rw [Real.log_div hUpos.ne' hApos.ne']
      linarith
    have hfirst : 1 / (A : ℝ) ≤ 1 / (B : ℝ) :=
      one_div_le_one_div_of_le hBpos hBAcast
    calc
      logFinsetMass (oddLogWindow A U) ≤
          ∑ N ∈ Finset.Icc A U, 1 / (N : ℝ) :=
        logFinsetMass_oddLogWindow_le_sum_Icc_reciprocal hA
      _ ≤ 1 / (A : ℝ) + Real.log ((U : ℝ) / (A : ℝ)) :=
        sum_Icc_reciprocal_le_one_div_add_log_div hA hAU
      _ ≤ 1 / (B : ℝ) + 2 / (B : ℝ) := add_le_add hfirst hlogShell
      _ = 3 / (B : ℝ) := by ring
  · have hUA : U < A := by omega
    have hempty : oddLogWindow A U = ∅ := by
      simp [oddLogWindow, Finset.Icc_eq_empty_of_lt hUA]
    rw [hempty]
    simpa [logFinsetMass] using
      (div_nonneg (show (0 : ℝ) ≤ 3 by norm_num) hBpos.le)

private theorem natCast_ceil_sub_one_le {z : ℝ} (hz : 0 < z) :
    ((Nat.ceil z - 1 : ℕ) : ℝ) ≤ z := by
  have hceil : (Nat.ceil z : ℝ) < z + 1 := Nat.ceil_lt_add_one hz.le
  have hceilPos : 1 ≤ Nat.ceil z := by
    have : (0 : ℝ) < Nat.ceil z := lt_of_lt_of_le hz (Nat.le_ceil z)
    exact_mod_cast this
  push_cast [Nat.cast_sub hceilPos]
  linarith

private theorem le_natCast_floor_add_one (z : ℝ) :
    z ≤ ((Nat.floor z + 1 : ℕ) : ℝ) := by
  push_cast
  exact (Nat.lt_floor_add_one z).le

/-- Rounding the two endpoints of an ordered real-power window changes its
logarithmic source mass by at most `6 / B`.  The two `3 / B` contributions are
the lower and upper endpoint shells. -/
theorem logFinsetSymmDiffMass_taoNyOddWindow_rpow_le_six_div
    {B : ℕ} {x beta alpha : ℝ}
    (hB : 1 ≤ B) (hBx : (B : ℝ) ≤ x) (hxB : x ≤ (B : ℝ) + 1)
    (hbetaOne : 1 ≤ beta) (hbetaTwo : beta ≤ 2)
    (halphaNonneg : 0 ≤ alpha)
    (hprodOne : 1 ≤ beta * alpha) (hprodTwo : beta * alpha ≤ 2) :
    logFinsetSymmDiffMass
        (taoNyOddWindow ((B : ℝ) ^ beta) alpha)
        (taoNyOddWindow (x ^ beta) alpha) ≤
      6 / (B : ℝ) := by
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hxpos : 0 < x := hBpos.trans_le hBx
  have hbetaNonneg : 0 ≤ beta := by linarith
  have hBpowPos : 0 < (B : ℝ) ^ beta := Real.rpow_pos_of_pos hBpos beta
  have hxpowPos : 0 < x ^ beta := Real.rpow_pos_of_pos hxpos beta
  have hinner : (B : ℝ) ^ beta ≤ x ^ beta :=
    Real.rpow_le_rpow hBpos.le hBx hbetaNonneg
  have houter : ((B : ℝ) ^ beta) ^ alpha ≤ (x ^ beta) ^ alpha :=
    Real.rpow_le_rpow hBpowPos.le hinner halphaNonneg
  have hlo : Nat.ceil ((B : ℝ) ^ beta) ≤ Nat.ceil (x ^ beta) :=
    Nat.ceil_mono hinner
  have hhi : Nat.floor (((B : ℝ) ^ beta) ^ alpha) ≤
      Nat.floor ((x ^ beta) ^ alpha) := Nat.floor_mono houter
  have hlower :
      logFinsetMass
          (oddLogWindow (Nat.ceil ((B : ℝ) ^ beta))
            (Nat.ceil (x ^ beta) - 1)) ≤
        3 / (B : ℝ) := by
    apply logFinsetMass_oddLogWindow_le_three_div_of_floor_shell
      hB hBx hxB hbetaOne hbetaTwo
    · exact Nat.le_ceil ((B : ℝ) ^ beta)
    · exact natCast_ceil_sub_one_le hxpowPos
  have hupper :
      logFinsetMass
          (oddLogWindow (Nat.floor (((B : ℝ) ^ beta) ^ alpha) + 1)
            (Nat.floor ((x ^ beta) ^ alpha))) ≤
        3 / (B : ℝ) := by
    apply logFinsetMass_oddLogWindow_le_three_div_of_floor_shell
      hB hBx hxB hprodOne hprodTwo
    · rw [← Real.rpow_mul hBpos.le]
      exact le_natCast_floor_add_one ((B : ℝ) ^ (beta * alpha))
    · rw [← Real.rpow_mul hxpos.le]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le (beta * alpha))
  have hshells := logFinsetSymmDiffMass_oddLogWindow_le_shells hlo hhi
  change logFinsetSymmDiffMass
      (oddLogWindow (Nat.ceil ((B : ℝ) ^ beta))
        (Nat.floor (((B : ℝ) ^ beta) ^ alpha)))
      (oddLogWindow (Nat.ceil (x ^ beta))
        (Nat.floor ((x ^ beta) ^ alpha))) ≤ 6 / (B : ℝ)
  calc
    logFinsetSymmDiffMass
        (oddLogWindow (Nat.ceil ((B : ℝ) ^ beta))
          (Nat.floor (((B : ℝ) ^ beta) ^ alpha)))
        (oddLogWindow (Nat.ceil (x ^ beta))
          (Nat.floor ((x ^ beta) ^ alpha))) ≤
        logFinsetMass
            (oddLogWindow (Nat.ceil ((B : ℝ) ^ beta))
              (Nat.ceil (x ^ beta) - 1)) +
          logFinsetMass
            (oddLogWindow (Nat.floor (((B : ℝ) ^ beta) ^ alpha) + 1)
              (Nat.floor ((x ^ beta) ^ alpha))) := hshells
    _ ≤ 3 / (B : ℝ) + 3 / (B : ℝ) := add_le_add hlower hupper
    _ = 6 / (B : ℝ) := by ring

/-- The ordered-window estimate specialized to `B = floor x`. -/
theorem logFinsetSymmDiffMass_taoNyOddWindow_floor_rpow_le_six_div
    {x beta alpha : ℝ} (hx : 1 ≤ x)
    (hbetaOne : 1 ≤ beta) (hbetaTwo : beta ≤ 2)
    (halphaNonneg : 0 ≤ alpha)
    (hprodOne : 1 ≤ beta * alpha) (hprodTwo : beta * alpha ≤ 2) :
    logFinsetSymmDiffMass
        (taoNyOddWindow (((Nat.floor x : ℕ) : ℝ) ^ beta) alpha)
        (taoNyOddWindow (x ^ beta) alpha) ≤
      6 / ((Nat.floor x : ℕ) : ℝ) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hB : 1 ≤ Nat.floor x :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)
  apply logFinsetSymmDiffMass_taoNyOddWindow_rpow_le_six_div
    hB (Nat.floor_le hx0) (Nat.lt_floor_add_one x).le
    hbetaOne hbetaTwo halphaNonneg hprodOne hprodTwo

/-- The first Proposition 1.11 source scale, `beta = alpha`, has the sharp
`6 / floor x` weighted support perturbation. -/
theorem logFinsetSymmDiffMass_taoNyOddWindow_floor_taoAlpha_le_six_div
    {x : ℝ} (hx : 1 ≤ x) :
    logFinsetSymmDiffMass
        (taoNyOddWindow
          (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha) taoAlpha)
        (taoNyOddWindow (x ^ taoAlpha) taoAlpha) ≤
      6 / ((Nat.floor x : ℕ) : ℝ) := by
  apply logFinsetSymmDiffMass_taoNyOddWindow_floor_rpow_le_six_div hx
  all_goals norm_num [taoAlpha]

/-- The second Proposition 1.11 source scale, `beta = alpha^2`, obeys the
same uniform weighted support perturbation. -/
theorem logFinsetSymmDiffMass_taoNyOddWindow_floor_taoAlpha_sq_le_six_div
    {x : ℝ} (hx : 1 ≤ x) :
    logFinsetSymmDiffMass
        (taoNyOddWindow
          (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)) taoAlpha)
        (taoNyOddWindow (x ^ (taoAlpha ^ 2)) taoAlpha) ≤
      6 / ((Nat.floor x : ℕ) : ℝ) := by
  apply logFinsetSymmDiffMass_taoNyOddWindow_floor_rpow_le_six_div hx
  all_goals norm_num [taoAlpha]

/-- A `6 / B` weighted support error and the standard `log B / 8000`
normalizer lower bound give the sharp uniform event error
`96000 / (B * log B)`. -/
theorem abs_logFinsetProb_sub_le_ninetySixThousand_div_mul_log
    {B : ℕ} {S T : Finset ℕ}
    (hB : 1 ≤ B) (hlog : 0 < Real.log (B : ℝ))
    (hsymm : logFinsetSymmDiffMass S T ≤ 6 / (B : ℝ))
    (hmassS : Real.log (B : ℝ) / 8000 ≤ logFinsetMass S)
    (hmassT : Real.log (B : ℝ) / 8000 ≤ logFinsetMass T)
    (E : Set ℕ) :
    |logFinsetProb S E - logFinsetProb T E| ≤
      96000 / ((B : ℝ) * Real.log (B : ℝ)) := by
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hbasePos : 0 < Real.log (B : ℝ) / 8000 := div_pos hlog (by norm_num)
  have hSpos : 0 < logFinsetMass S := hbasePos.trans_le hmassS
  have hTpos : 0 < logFinsetMass T := hbasePos.trans_le hmassT
  have hmin : Real.log (B : ℝ) / 8000 ≤
      min (logFinsetMass S) (logFinsetMass T) := le_min hmassS hmassT
  have hminPos : 0 < min (logFinsetMass S) (logFinsetMass T) :=
    hbasePos.trans_le hmin
  have hnum :
      2 * logFinsetSymmDiffMass S T ≤ 12 / (B : ℝ) := by
    calc
      2 * logFinsetSymmDiffMass S T ≤ 2 * (6 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hsymm (by norm_num)
      _ = 12 / (B : ℝ) := by ring
  have hnumNonneg : 0 ≤ 12 / (B : ℝ) :=
    div_nonneg (by norm_num) hBpos.le
  calc
    |logFinsetProb S E - logFinsetProb T E| ≤
        2 * logFinsetSymmDiffMass S T /
          min (logFinsetMass S) (logFinsetMass T) :=
      abs_logFinsetProb_sub_le_two_symmDiffMass_div_min hSpos hTpos E
    _ ≤ (12 / (B : ℝ)) /
        min (logFinsetMass S) (logFinsetMass T) :=
      div_le_div_of_nonneg_right hnum hminPos.le
    _ ≤ (12 / (B : ℝ)) / (Real.log (B : ℝ) / 8000) :=
      div_le_div_of_nonneg_left hnumNonneg hbasePos hmin
    _ = 96000 / ((B : ℝ) * Real.log (B : ℝ)) := by
      field_simp [hBpos.ne', hlog.ne']
      norm_num

/-- Normalized real-to-floor source perturbation for a general power scale
whose two endpoint exponents lie in `[1, 2]`. -/
theorem abs_logFinsetProb_taoNyOddWindow_floor_rpow_sub_le
    {x beta alpha : ℝ} (hx : 1 ≤ x)
    (hbetaOne : 1 ≤ beta) (hbetaTwo : beta ≤ 2)
    (halphaNonneg : 0 ≤ alpha)
    (hprodOne : 1 ≤ beta * alpha) (hprodTwo : beta * alpha ≤ 2)
    (hlog : 0 < Real.log ((Nat.floor x : ℕ) : ℝ))
    (hmassFloor :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        logFinsetMass
          (taoNyOddWindow (((Nat.floor x : ℕ) : ℝ) ^ beta) alpha))
    (hmassReal :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        logFinsetMass (taoNyOddWindow (x ^ beta) alpha))
    (E : Set ℕ) :
    |logFinsetProb
          (taoNyOddWindow (((Nat.floor x : ℕ) : ℝ) ^ beta) alpha) E -
        logFinsetProb (taoNyOddWindow (x ^ beta) alpha) E| ≤
      96000 /
        (((Nat.floor x : ℕ) : ℝ) *
          Real.log ((Nat.floor x : ℕ) : ℝ)) := by
  have hB : 1 ≤ Nat.floor x :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)
  exact abs_logFinsetProb_sub_le_ninetySixThousand_div_mul_log
    hB hlog
      (logFinsetSymmDiffMass_taoNyOddWindow_floor_rpow_le_six_div
        hx hbetaOne hbetaTwo halphaNonneg hprodOne hprodTwo)
      hmassFloor hmassReal E

/-- Normalized source perturbation at the first Proposition 1.11 scale. -/
theorem abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sub_le
    {x : ℝ} (hx : 1 ≤ x)
    (hlog : 0 < Real.log ((Nat.floor x : ℕ) : ℝ))
    (hmassFloor :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        logFinsetMass
          (taoNyOddWindow
            (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha) taoAlpha))
    (hmassReal :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        logFinsetMass (taoNyOddWindow (x ^ taoAlpha) taoAlpha))
    (E : Set ℕ) :
    |logFinsetProb
          (taoNyOddWindow
            (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha) taoAlpha) E -
        logFinsetProb (taoNyOddWindow (x ^ taoAlpha) taoAlpha) E| ≤
      96000 /
        (((Nat.floor x : ℕ) : ℝ) *
          Real.log ((Nat.floor x : ℕ) : ℝ)) := by
  apply abs_logFinsetProb_taoNyOddWindow_floor_rpow_sub_le hx
    (beta := taoAlpha) (alpha := taoAlpha)
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · exact hlog
  · exact hmassFloor
  · exact hmassReal

/-- Normalized source perturbation at the second Proposition 1.11 scale. -/
theorem abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sq_sub_le
    {x : ℝ} (hx : 1 ≤ x)
    (hlog : 0 < Real.log ((Nat.floor x : ℕ) : ℝ))
    (hmassFloor :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        logFinsetMass
          (taoNyOddWindow
            (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)) taoAlpha))
    (hmassReal :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        logFinsetMass (taoNyOddWindow (x ^ (taoAlpha ^ 2)) taoAlpha))
    (E : Set ℕ) :
    |logFinsetProb
          (taoNyOddWindow
            (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)) taoAlpha) E -
        logFinsetProb (taoNyOddWindow (x ^ (taoAlpha ^ 2)) taoAlpha) E| ≤
      96000 /
        (((Nat.floor x : ℕ) : ℝ) *
          Real.log ((Nat.floor x : ℕ) : ℝ)) := by
  apply abs_logFinsetProb_taoNyOddWindow_floor_rpow_sub_le hx
    (beta := taoAlpha ^ 2) (alpha := taoAlpha)
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · norm_num [taoAlpha]
  · exact hlog
  · exact hmassFloor
  · exact hmassReal

end

end Tao
end Erdos1135SecondScale
