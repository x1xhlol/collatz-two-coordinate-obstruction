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

import Erdos1135SecondScale.Tao.Probability.LogWindowSourceIndex
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Tao Logarithmic Window Endpoints

This module records the finite endpoint convention for Tao's windows
`N_y = Log(2N+1 in [y, y^alpha])`.  It keeps the support guards explicit:
the real-width lemmas below give sufficient positive-mass hypotheses but do
not claim eventual nonemptiness.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

/-- Tao's fixed exponent `alpha = 1.0005`. -/
noncomputable def taoAlpha : ℝ :=
  (2001 : ℝ) / 2000

/-- Lower natural endpoint for the odd value window attached to `y`. -/
noncomputable def taoNyLo (y : ℝ) : ℕ :=
  Nat.ceil y

/-- Upper natural endpoint for the odd value window attached to `y`. -/
noncomputable def taoNyHi (y alpha : ℝ) : ℕ :=
  Nat.floor (y ^ alpha)

/-- Odd values in Tao's finite logarithmic window with real endpoints. -/
noncomputable def taoNyOddWindow (y alpha : ℝ) : Finset ℕ :=
  oddLogWindow (taoNyLo y) (taoNyHi y alpha)

theorem taoNyOddWindow_mem_of_rpow_nonneg {y alpha : ℝ} {n : ℕ}
    (hpow : 0 ≤ y ^ alpha) :
    n ∈ taoNyOddWindow y alpha ↔
      y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y ^ alpha ∧ n % 2 = 1 := by
  unfold taoNyOddWindow taoNyLo taoNyHi
  rw [oddLogWindow_mem]
  constructor
  · rintro ⟨hlo, hhi, hodd⟩
    exact ⟨(Nat.ceil_le.mp hlo), (Nat.le_floor_iff hpow).mp hhi, hodd⟩
  · rintro ⟨hlo, hhi, hodd⟩
    exact ⟨(Nat.ceil_le.mpr hlo), (Nat.le_floor_iff hpow).mpr hhi, hodd⟩

theorem taoNyOddWindow_mem {y alpha : ℝ} {n : ℕ} (hy : 0 ≤ y) :
    n ∈ taoNyOddWindow y alpha ↔
      y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y ^ alpha ∧ n % 2 = 1 := by
  exact taoNyOddWindow_mem_of_rpow_nonneg (Real.rpow_nonneg hy alpha)

theorem oddLogWindow_mem_of_bounds_odd {lo hi n : ℕ}
    (hlo : lo ≤ n) (hhi : n ≤ hi) (hnodd : Odd n) :
    n ∈ oddLogWindow lo hi := by
  rw [oddLogWindow_mem]
  exact ⟨hlo, hhi, Nat.odd_iff.mp hnodd⟩

theorem oddLogWindow_nonempty_of_exists_odd {lo hi : ℕ}
    (h : ∃ n : ℕ, lo ≤ n ∧ n ≤ hi ∧ Odd n) :
    (oddLogWindow lo hi).Nonempty := by
  rcases h with ⟨n, hlo, hhi, hnodd⟩
  exact ⟨n, oddLogWindow_mem_of_bounds_odd hlo hhi hnodd⟩

theorem logFinsetMass_oddLogWindow_pos_of_exists_odd {lo hi : ℕ}
    (h : ∃ n : ℕ, lo ≤ n ∧ n ≤ hi ∧ Odd n) :
    0 < logFinsetMass (oddLogWindow lo hi) := by
  rcases h with ⟨n, hlo, hhi, hnodd⟩
  exact logFinsetMass_oddLogWindow_pos_of_mem
    (oddLogWindow_mem_of_bounds_odd hlo hhi hnodd)

theorem exists_odd_between_of_succ_le {lo hi : ℕ}
    (h : lo + 1 ≤ hi) :
    ∃ n : ℕ, lo ≤ n ∧ n ≤ hi ∧ Odd n := by
  by_cases hlo_odd : Odd lo
  · exact ⟨lo, le_rfl, by omega, hlo_odd⟩
  · have hlo_even : Even lo := Nat.not_odd_iff_even.mp hlo_odd
    exact ⟨lo + 1, by omega, h, hlo_even.add_one⟩

theorem oddLogWindow_nonempty_of_succ_le {lo hi : ℕ}
    (h : lo + 1 ≤ hi) :
    (oddLogWindow lo hi).Nonempty :=
  oddLogWindow_nonempty_of_exists_odd (exists_odd_between_of_succ_le h)

/-- Narrowing the natural endpoints narrows the inclusive odd window. -/
theorem oddLogWindow_mono {lo₁ hi₁ lo₂ hi₂ : ℕ}
    (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) :
    oddLogWindow lo₁ hi₁ ⊆ oddLogWindow lo₂ hi₂ := by
  intro n hn
  rw [oddLogWindow_mem] at hn ⊢
  exact ⟨hlo.trans hn.1, hn.2.1.trans hhi, hn.2.2⟩

/-- A real interval with two units of room contains an odd natural after
rounding its endpoints outward. -/
theorem oddLogWindow_ceil_floor_nonempty_of_add_two_le
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hwidth : lower + 2 ≤ upper) :
    (oddLogWindow (Nat.ceil lower) (Nat.floor upper)).Nonempty := by
  apply oddLogWindow_nonempty_of_succ_le
  apply Nat.le_floor
  have hceil := Nat.ceil_lt_add_one hlower
  norm_num at hceil ⊢
  linarith

theorem logFinsetMass_oddLogWindow_pos_of_succ_le {lo hi : ℕ}
    (h : lo + 1 ≤ hi) :
    0 < logFinsetMass (oddLogWindow lo hi) :=
  logFinsetMass_oddLogWindow_pos_of_exists_odd (exists_odd_between_of_succ_le h)

theorem logFinsetMass_oddLogWindow_ceil_floor_pos_of_add_two_le
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hwidth : lower + 2 ≤ upper) :
    0 < logFinsetMass
      (oddLogWindow (Nat.ceil lower) (Nat.floor upper)) := by
  have hnonempty :=
    oddLogWindow_ceil_floor_nonempty_of_add_two_le hlower hwidth
  rcases hnonempty with ⟨n, hn⟩
  exact logFinsetMass_oddLogWindow_pos_of_mem hn

theorem taoNyLo_succ_le_taoNyHi_of_width {y alpha : ℝ}
    (hy : 0 ≤ y) (hgap : y + 2 ≤ y ^ alpha) :
    taoNyLo y + 1 ≤ taoNyHi y alpha := by
  have hceil_lt : ((taoNyLo y : ℕ) : ℝ) < y + 1 := by
    unfold taoNyLo
    exact Nat.ceil_lt_add_one hy
  have hsucc_lt : (((taoNyLo y + 1 : ℕ) : ℕ) : ℝ) < y + 2 := by
    norm_num
    linarith
  have hsucc_le_pow : ((taoNyLo y + 1 : ℕ) : ℝ) ≤ y ^ alpha :=
    le_trans (le_of_lt hsucc_lt) hgap
  unfold taoNyHi
  exact Nat.le_floor hsucc_le_pow

/-- A real factor-two width estimate yields the natural endpoint width used
by the finite logarithmic-mass lower bound. -/
theorem taoNyLo_two_mul_le_taoNyHi_of_width {y alpha : ℝ}
    (hy : 0 ≤ y) (hgap : 2 * y + 2 ≤ y ^ alpha) :
    2 * taoNyLo y ≤ taoNyHi y alpha := by
  have hceil_lt : ((taoNyLo y : ℕ) : ℝ) < y + 1 := by
    unfold taoNyLo
    exact Nat.ceil_lt_add_one hy
  have hdouble_lt :
      (2 : ℝ) * (taoNyLo y : ℝ) < 2 * y + 2 := by
    nlinarith
  have hdouble_le :
      (((2 * taoNyLo y : ℕ) : ℕ) : ℝ) ≤ y ^ alpha := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact (le_of_lt hdouble_lt).trans hgap
  unfold taoNyHi
  exact Nat.le_floor hdouble_le

theorem taoNyOddWindow_nonempty_of_width {y alpha : ℝ}
    (hy : 0 ≤ y) (hgap : y + 2 ≤ y ^ alpha) :
    (taoNyOddWindow y alpha).Nonempty := by
  have hsucc_le := taoNyLo_succ_le_taoNyHi_of_width hy hgap
  unfold taoNyOddWindow
  exact oddLogWindow_nonempty_of_succ_le hsucc_le

theorem logFinsetMass_taoNyOddWindow_pos_of_width {y alpha : ℝ}
    (hy : 0 ≤ y) (hgap : y + 2 ≤ y ^ alpha) :
    0 < logFinsetMass (taoNyOddWindow y alpha) := by
  have hsucc_le := taoNyLo_succ_le_taoNyHi_of_width hy hgap
  unfold taoNyOddWindow
  exact logFinsetMass_oddLogWindow_pos_of_succ_le hsucc_le

theorem taoAlpha_one_lt : 1 < taoAlpha := by
  norm_num [taoAlpha]

theorem taoAlpha_pos : 0 < taoAlpha := by
  norm_num [taoAlpha]

theorem taoAlpha_sq_pos : 0 < taoAlpha ^ 2 :=
  pow_pos taoAlpha_pos 2

theorem real_width_support_eventually_of_one_lt {alpha : ℝ} (halpha : 1 < alpha) :
    ∀ᶠ y : ℝ in atTop, y + 2 ≤ y ^ alpha := by
  have hpow : Tendsto (fun y : ℝ => y ^ (alpha - 1)) atTop atTop := by
    exact tendsto_rpow_atTop (sub_pos.mpr halpha)
  filter_upwards [hpow.eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2 : ℝ)]
    with y hy2 hy
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hy
  have hmul : y * 2 ≤ y * y ^ (alpha - 1) := by
    exact mul_le_mul_of_nonneg_left hy2 (le_of_lt hypos)
  have htwoy : y + 2 ≤ y * 2 := by
    nlinarith
  have hprod : y * y ^ (alpha - 1) = y ^ alpha := by
    calc
      y * y ^ (alpha - 1) = y ^ (1 : ℝ) * y ^ (alpha - 1) := by
        simp [Real.rpow_one]
      _ = y ^ (1 + (alpha - 1)) := by
        exact (Real.rpow_add hypos 1 (alpha - 1)).symm
      _ = y ^ alpha := by
        ring_nf
  calc
    y + 2 ≤ y * 2 := htwoy
    _ ≤ y * y ^ (alpha - 1) := hmul
    _ = y ^ alpha := hprod

/-- Eventually a positive-power window has factor-two natural endpoint room. -/
theorem real_two_mul_width_eventually_of_one_lt
    {alpha : ℝ} (halpha : 1 < alpha) :
    ∀ᶠ y : ℝ in atTop, 2 * y + 2 ≤ y ^ alpha := by
  have hpow : Tendsto (fun y : ℝ => y ^ (alpha - 1)) atTop atTop := by
    exact tendsto_rpow_atTop (sub_pos.mpr halpha)
  filter_upwards [hpow.eventually_ge_atTop (3 : ℝ), eventually_ge_atTop (2 : ℝ)]
    with y hy3 hy
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hy
  have hmul : y * 3 ≤ y * y ^ (alpha - 1) := by
    exact mul_le_mul_of_nonneg_left hy3 hypos.le
  have hthree : 2 * y + 2 ≤ y * 3 := by
    nlinarith
  have hprod : y * y ^ (alpha - 1) = y ^ alpha := by
    calc
      y * y ^ (alpha - 1) = y ^ (1 : ℝ) * y ^ (alpha - 1) := by
        simp [Real.rpow_one]
      _ = y ^ (1 + (alpha - 1)) := by
        exact (Real.rpow_add hypos 1 (alpha - 1)).symm
      _ = y ^ alpha := by ring_nf
  exact hthree.trans (hmul.trans_eq hprod)

theorem nat_width_support_eventually_of_one_lt {alpha : ℝ} (halpha : 1 < alpha) :
    ∀ᶠ B : ℕ in atTop, (B : ℝ) + 2 ≤ (B : ℝ) ^ alpha := by
  exact tendsto_natCast_atTop_atTop.eventually
    (real_width_support_eventually_of_one_lt halpha)

theorem taoNy_width_eventually :
    ∀ᶠ y : ℝ in atTop, y + 2 ≤ y ^ taoAlpha :=
  real_width_support_eventually_of_one_lt taoAlpha_one_lt

theorem taoNat_width_eventually :
    ∀ᶠ B : ℕ in atTop, (B : ℝ) + 2 ≤ (B : ℝ) ^ taoAlpha :=
  nat_width_support_eventually_of_one_lt taoAlpha_one_lt

theorem support_guard_comp_nat_rpow {alpha beta : ℝ}
    (hguard : ∀ᶠ y : ℝ in atTop, y + 2 ≤ y ^ alpha)
    (hbeta : 0 < beta) :
    ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ beta + 2 ≤ ((B : ℝ) ^ beta) ^ alpha := by
  exact ((tendsto_rpow_atTop hbeta).comp tendsto_natCast_atTop_atTop).eventually hguard

theorem two_mul_support_guard_comp_nat_rpow {alpha beta : ℝ}
    (hguard : ∀ᶠ y : ℝ in atTop, 2 * y + 2 ≤ y ^ alpha)
    (hbeta : 0 < beta) :
    ∀ᶠ B : ℕ in atTop,
      2 * ((B : ℝ) ^ beta) + 2 ≤ ((B : ℝ) ^ beta) ^ alpha := by
  exact ((tendsto_rpow_atTop hbeta).comp tendsto_natCast_atTop_atTop).eventually hguard

theorem eventually_taoNyOddWindow_mass_pos :
    ∀ᶠ y : ℝ in atTop,
      0 < logFinsetMass (taoNyOddWindow y taoAlpha) := by
  filter_upwards [taoNy_width_eventually, eventually_ge_atTop (0 : ℝ)] with y hwidth hy
  exact logFinsetMass_taoNyOddWindow_pos_of_width hy hwidth

end Tao
end Erdos1135SecondScale
