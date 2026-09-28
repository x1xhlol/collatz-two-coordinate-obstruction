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

import Erdos1135SecondScale.Tao.Probability.LogWindowBoundaryMass

/-!
Quarter-width refinement of Mazur's rounded-window mass argument, used by
the independently checked alpha = 2001/2000 specialization. The proof is
adapted from the pinned companion's one-eighth-width lemma; the stronger
conclusion uses the explicitly stronger width threshold 12.
-/

namespace Erdos1135SecondScale.Tao

private theorem log_two_lt_one_quarter : Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

theorem one_quarter_log_width_le_rounded_power_oddWindow_mass
    {y alpha : ℝ} (hy : 2 ≤ y) (halpha : 1 < alpha)
    (hab : Nat.ceil y ≤ Nat.floor (Real.rpow y alpha))
    (hwidth : 12 ≤ (alpha - 1) * Real.log y) :
    ((alpha - 1) / 4) * Real.log y ≤
      logFinsetMass
        (oddLogWindow (Nat.ceil y) (Nat.floor (Real.rpow y alpha))) := by
  let a := Nat.ceil y
  let z := Real.rpow y alpha
  let b := Nat.floor z
  have hyPos : 0 < y := by linarith
  have hyOne : 1 ≤ y := by linarith
  have hzPos : 0 < z := by
    dsimp [z]
    exact Real.rpow_pos_of_pos hyPos _
  have hyLeZ : y ≤ z := by
    dsimp [z]
    exact Real.self_le_rpow_of_one_le hyOne halpha.le
  have haReal : y ≤ (a : ℝ) := by
    dsimp [a]
    exact Nat.le_ceil y
  have haUpper : (a : ℝ) ≤ 2 * y := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ y)
    dsimp [a]
    nlinarith
  have haNat : 2 ≤ a := by
    exact_mod_cast hy.trans haReal
  have hbLower : z / 2 ≤ (b : ℝ) := by
    have hfloor := Nat.lt_floor_add_one z
    dsimp [b]
    nlinarith [hyLeZ, hy]
  have hbPos : (0 : ℝ) < b := by
    nlinarith [hbLower, hzPos]
  have haPos : (0 : ℝ) < a := by positivity
  have hlogA : Real.log (a : ℝ) ≤ Real.log 2 + Real.log y := by
    have hmono := Real.strictMonoOn_log.monotoneOn haPos
      (mul_pos (by norm_num) hyPos) haUpper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne'] at hmono
    exact hmono
  have hlogB : alpha * Real.log y - Real.log 2 ≤ Real.log (b : ℝ) := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (div_pos hzPos (by norm_num)) hbPos hbLower
    rw [Real.log_div hzPos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    have hlogZ : Real.log z = alpha * Real.log y := by
      dsimp [z]
      exact Real.log_rpow hyPos _
    rw [hlogZ] at hmono
    exact hmono
  have hnatural :=
    half_log_ratio_sub_two_le_logFinsetMass_oddLogWindow haNat hab
  have hgap :
      (alpha - 1) * Real.log y - 2 * Real.log 2 ≤
        Real.log (b : ℝ) - Real.log (a : ℝ) := by
    nlinarith [hlogA, hlogB]
  have hmassBase :
      (1 / 2 : ℝ) * ((alpha - 1) * Real.log y) - 3 ≤
        logFinsetMass (oddLogWindow a b) := by
    nlinarith [hnatural, hgap, log_two_lt_one_quarter]
  dsimp [a, b, z] at hmassBase ⊢
  nlinarith [hmassBase, hwidth]


end Erdos1135SecondScale.Tao
