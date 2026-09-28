import Erdos1135.Tao.Probability.LogWindowMassLower
import Erdos1135.Tao.Probability.LogWindowEndpoints
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 5 Common-Threshold Schedule

This module fixes Tao's two logarithmic source branches over one natural
threshold `B`.  The scale `n0`, ambient exponent `nPrime`, and eventual
threshold are shared by both branches.  It contains no residue PMF,
Proposition 1.9 output packet, or no-hit consumer.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

/-- The two source windows used together in Tao's Section 5. -/
inductive TaoSection5SourceBranch
  | alpha
  | alphaSq
  deriving DecidableEq, Fintype

/-- Branch-specific source scale over the shared natural threshold. -/
noncomputable def taoSection5SourceY
    (B : ℕ) : TaoSection5SourceBranch → ℝ
  | .alpha => (B : ℝ) ^ taoAlpha
  | .alphaSq => (B : ℝ) ^ (taoAlpha ^ 2)

/-- Tao's executable Section 5 scale. -/
def taoSection5N0 (B : ℕ) : ℕ :=
  Nat.log 2 B / 10

/-- The Proposition 1.9 ambient exponent `n' = 3*n0`. -/
def taoSection5NPrime (B : ℕ) : ℕ :=
  3 * taoSection5N0 B

noncomputable def taoSection5SourceLo
    (B : ℕ) (branch : TaoSection5SourceBranch) : ℕ :=
  taoNyLo (taoSection5SourceY B branch)

noncomputable def taoSection5SourceHi
    (B : ℕ) (branch : TaoSection5SourceBranch) : ℕ :=
  taoNyHi (taoSection5SourceY B branch) taoAlpha

/-- The natural-log implementation is exactly Tao's displayed real-floor
formula, including the zero and one endpoints. -/
theorem taoSection5N0_eq_floor_log (B : ℕ) :
    taoSection5N0 B =
      Nat.floor (Real.log B / (10 * Real.log 2)) := by
  rw [mul_comm (10 : ℝ) (Real.log 2), ← div_div]
  change Nat.log 2 B / 10 = Nat.floor (Real.logb 2 B / (10 : ℝ))
  calc
    Nat.log 2 B / 10 = Nat.floor (Real.logb 2 B) / 10 := by
      exact congrArg (fun n : ℕ => n / 10)
        (Real.natFloor_logb_natCast 2 B).symm
    _ = Nat.floor (Real.logb 2 B / (10 : ℝ)) := by
      exact (Nat.floor_div_natCast (Real.logb 2 B) 10).symm

/-- The same exact floor supplies the lower estimate needed by later no-hit
rate conversion. -/
theorem log_div_ten_log_two_sub_one_lt_taoSection5N0 (B : ℕ) :
    Real.log B / (10 * Real.log 2) - 1 < (taoSection5N0 B : ℝ) := by
  let x := Real.log B / (10 * Real.log 2)
  have hfloor : Nat.floor x = taoSection5N0 B :=
    (taoSection5N0_eq_floor_log B).symm
  have h := Nat.lt_floor_add_one x
  rw [hfloor] at h
  dsimp [x] at h ⊢
  nlinarith

theorem taoSection5N0_le_log_div_ten_log_two (B : ℕ) :
    (taoSection5N0 B : ℝ) ≤ Real.log B / (10 * Real.log 2) := by
  have hscaleNonneg : 0 ≤ Real.log B / (10 * Real.log 2) := by
    by_cases hB : B = 0
    · simp [hB]
    · have hBone : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hBone)) (by positivity)
  rw [taoSection5N0_eq_floor_log]
  exact Nat.floor_le hscaleNonneg

theorem taoSection5N0_one_le_of_pow_ten_le
    {B : ℕ} (hB : 2 ^ 10 ≤ B) :
    1 ≤ taoSection5N0 B := by
  have hlog : 10 ≤ Nat.log 2 B :=
    Nat.le_log_of_pow_le (by norm_num) hB
  unfold taoSection5N0
  omega

/-- Quadratic room is branch-independent and already holds at every positive
threshold; positive ambient exponent is imposed separately. -/
theorem taoSection5NPrime_sq_pow_le_threshold
    {B : ℕ} (hB : 1 ≤ B) :
    (2 ^ taoSection5NPrime B) ^ 2 ≤ B := by
  have hexp : taoSection5NPrime B * 2 ≤ Nat.log 2 B := by
    unfold taoSection5NPrime taoSection5N0
    omega
  calc
    (2 ^ taoSection5NPrime B) ^ 2 = 2 ^ (taoSection5NPrime B * 2) := by
      rw [pow_mul]
    _ ≤ 2 ^ Nat.log 2 B := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ B := Nat.pow_log_le_self 2 (Nat.ne_of_gt hB)

theorem taoSection5Threshold_le_sourceLo
    {B : ℕ} (hB : 1 ≤ B) (branch : TaoSection5SourceBranch) :
    B ≤ taoSection5SourceLo B branch := by
  cases branch with
  | alpha =>
      change B ≤ Nat.ceil ((B : ℝ) ^ taoAlpha)
      have hreal : (B : ℝ) ≤ (B : ℝ) ^ taoAlpha :=
        Real.self_le_rpow_of_one_le (by exact_mod_cast hB) taoAlpha_one_lt.le
      simpa using Nat.ceil_le_ceil hreal
  | alphaSq =>
      change B ≤ Nat.ceil ((B : ℝ) ^ (taoAlpha ^ 2))
      have halphaSq : (1 : ℝ) ≤ taoAlpha ^ 2 := by
        nlinarith [taoAlpha_one_lt]
      have hreal : (B : ℝ) ≤ (B : ℝ) ^ (taoAlpha ^ 2) :=
        Real.self_le_rpow_of_one_le (by exact_mod_cast hB) halphaSq
      simpa using Nat.ceil_le_ceil hreal

/-- Both source branches eventually have the factor-two natural endpoint
width needed by the finite mass theorem. -/
theorem eventually_taoSection5Source_two_mul_lo_le_hi :
    ∀ᶠ B : ℕ in atTop,
      ∀ branch : TaoSection5SourceBranch,
        2 * taoSection5SourceLo B branch ≤ taoSection5SourceHi B branch := by
  let hguard := real_two_mul_width_eventually_of_one_lt taoAlpha_one_lt
  have hfirst := two_mul_support_guard_comp_nat_rpow hguard taoAlpha_pos
  have hsecond := two_mul_support_guard_comp_nat_rpow hguard taoAlpha_sq_pos
  filter_upwards [hfirst, hsecond] with B hfirstB hsecondB
  intro branch
  cases branch with
  | alpha =>
      exact taoNyLo_two_mul_le_taoNyHi_of_width
        (Real.rpow_nonneg (Nat.cast_nonneg B) taoAlpha) hfirstB
  | alphaSq =>
      exact taoNyLo_two_mul_le_taoNyHi_of_width
        (Real.rpow_nonneg (Nat.cast_nonneg B) (taoAlpha ^ 2)) hsecondB

/-- One common schedule packet for both Section 5 source branches. -/
structure TaoSection5ResidueScheduleFacts (B : ℕ) : Prop where
  one_le_B : 1 ≤ B
  one_le_n0 : 1 ≤ taoSection5N0 B
  one_le_lo : ∀ branch, 1 ≤ taoSection5SourceLo B branch
  width : ∀ branch,
    2 * taoSection5SourceLo B branch ≤ taoSection5SourceHi B branch
  room_to_threshold : (2 ^ taoSection5NPrime B) ^ 2 ≤ B
  room : ∀ branch,
    (2 ^ taoSection5NPrime B) ^ 2 ≤ taoSection5SourceLo B branch

theorem TaoSection5ResidueScheduleFacts.one_le_nPrime
    {B : ℕ} (facts : TaoSection5ResidueScheduleFacts B) :
  1 ≤ taoSection5NPrime B := by
  unfold taoSection5NPrime
  have hn0 := facts.one_le_n0
  omega

theorem eventually_taoSection5ResidueScheduleFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5ResidueScheduleFacts B := by
  filter_upwards [eventually_ge_atTop (2 ^ 10 : ℕ),
    eventually_taoSection5Source_two_mul_lo_le_hi] with B hB hwidth
  have hB1 : 1 ≤ B := by omega
  have hn0 := taoSection5N0_one_le_of_pow_ten_le hB
  have hroomB := taoSection5NPrime_sq_pow_le_threshold hB1
  have hlo (branch : TaoSection5SourceBranch) :
      1 ≤ taoSection5SourceLo B branch :=
    hB1.trans (taoSection5Threshold_le_sourceLo hB1 branch)
  exact
    { one_le_B := hB1
      one_le_n0 := hn0
      one_le_lo := hlo
      width := hwidth
      room_to_threshold := hroomB
      room := fun branch =>
        hroomB.trans (taoSection5Threshold_le_sourceLo hB1 branch) }

theorem TaoSection5ResidueScheduleFacts.mass_lower
    {B : ℕ} (facts : TaoSection5ResidueScheduleFacts B)
    (branch : TaoSection5SourceBranch) :
    (1 / 4 : ℝ) ≤ logFinsetMass
      (oddLogWindow (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch)) :=
  one_fourth_le_logFinsetMass_oddLogWindow
    (facts.one_le_lo branch) (facts.width branch)

theorem TaoSection5ResidueScheduleFacts.mass_pos
    {B : ℕ} (facts : TaoSection5ResidueScheduleFacts B)
    (branch : TaoSection5SourceBranch) :
    0 < logFinsetMass
      (oddLogWindow (taoSection5SourceLo B branch)
        (taoSection5SourceHi B branch)) :=
  logFinsetMass_oddLogWindow_pos_of_two_mul_le
    (facts.one_le_lo branch) (facts.width branch)

example : taoSection5N0 0 = 0 := by decide
example : taoSection5N0 1 = 0 := by decide
example : taoSection5N0 1023 = 0 := by decide
example : taoSection5N0 1024 = 1 := by decide
example : taoSection5NPrime 1024 = 3 := by decide

end Tao
end Erdos1135
