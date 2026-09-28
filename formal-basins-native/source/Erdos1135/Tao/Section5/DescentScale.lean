import Erdos1135.Tao.Section5.FiveStepCompression
import Erdos1135.Tao.Section5.Schedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Section 5 Deterministic Descent Scales

This leaf owns the natural-log quotient ledger, branch-uniform source support,
and real-power absorption needed after five-step compression.  It contains no
PMF event assembly or no-hit theorem.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

/-- Five-step quotient of Tao's Section 5 iteration count. -/
def taoSection5DescentQ (B : ℕ) : ℕ :=
  taoSection5N0 B / 5

/-- Power-of-two exponent supplied by five-step compression. -/
def taoSection5DescentE (B : ℕ) : ℕ :=
  8 * taoSection5DescentQ B + 2 * (taoSection5N0 B % 5)

theorem taoSection5DescentQ_eq_log_div_fifty (B : ℕ) :
    taoSection5DescentQ B = Nat.log 2 B / 50 := by
  unfold taoSection5DescentQ taoSection5N0
  rw [Nat.div_div_eq_div_mul]

theorem log_add_one_le_fifty_mul_descentQ_add_one (B : ℕ) :
    Nat.log 2 B + 1 ≤ 50 * (taoSection5DescentQ B + 1) := by
  rw [taoSection5DescentQ_eq_log_div_fifty]
  have hdecomp := Nat.div_add_mod (Nat.log 2 B) 50
  have hrem := Nat.mod_lt (Nat.log 2 B) (by norm_num : 0 < 50)
  omega

theorem threshold_lt_two_pow_log_succ
    (B : ℕ) :
    B < 2 ^ (Nat.log 2 B + 1) := by
  exact Nat.lt_pow_succ_log_self (by norm_num) B

theorem two_pow_log_succ_le_descentQ_bound (B : ℕ) :
    2 ^ (Nat.log 2 B + 1) ≤
      2 ^ (50 * (taoSection5DescentQ B + 1)) :=
  Nat.pow_le_pow_right (by norm_num)
    (log_add_one_le_fifty_mul_descentQ_add_one B)

/-- The quotient floor leaves enough positive exponent room for the
`7/500` split used in the public main-term estimate. -/
theorem seven_div_five_hundred_mul_log_succ_lt_descentQ_succ (B : ℕ) :
    (7 / 500 : ℝ) * (Nat.log 2 B + 1 : ℕ) <
      ((taoSection5DescentQ B + 1 : ℕ) : ℝ) := by
  have hcast :
      ((Nat.log 2 B + 1 : ℕ) : ℝ) ≤
        (50 : ℝ) * ((taoSection5DescentQ B + 1 : ℕ) : ℝ) := by
    exact_mod_cast log_add_one_le_fifty_mul_descentQ_add_one B
  have hq : 0 < ((taoSection5DescentQ B + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-- Positive-exponent form of the logarithmic floor bridge. -/
theorem threshold_rpow_seven_div_five_hundred_lt_two_pow_descentQ_succ
    (B : ℕ) :
    (B : ℝ) ^ (7 / 500 : ℝ) <
      (2 : ℝ) ^ (taoSection5DescentQ B + 1 : ℕ) := by
  have hnat := threshold_lt_two_pow_log_succ B
  have hreal :
      (B : ℝ) < (2 : ℝ) ^ (Nat.log 2 B + 1 : ℕ) := by
    exact_mod_cast hnat
  have hpow := Real.rpow_lt_rpow (Nat.cast_nonneg B) hreal
    (by norm_num : 0 < (7 / 500 : ℝ))
  have hexp := seven_div_five_hundred_mul_log_succ_lt_descentQ_succ B
  calc
    (B : ℝ) ^ (7 / 500 : ℝ) <
        ((2 : ℝ) ^ (Nat.log 2 B + 1 : ℕ)) ^ (7 / 500 : ℝ) := hpow
    _ = ((2 : ℝ) ^ (((Nat.log 2 B + 1 : ℕ) : ℝ))) ^
        (7 / 500 : ℝ) := by
      rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^
        (((Nat.log 2 B + 1 : ℕ) : ℝ) * (7 / 500 : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ < (2 : ℝ) ^
        (((taoSection5DescentQ B + 1 : ℕ) : ℝ)) := by
      apply Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)
      nlinarith
    _ = (2 : ℝ) ^ (taoSection5DescentQ B + 1 : ℕ) :=
      Real.rpow_natCast (2 : ℝ) (taoSection5DescentQ B + 1)

/-- The quotient-sized denominator gain dominates a negative one-fiftieth
power of every positive threshold. -/
private theorem one_div_two_pow_descentQ_succ_lt_rpow_neg_one_fiftieth
    {B : ℕ} (hB : 1 ≤ B) :
    (1 : ℝ) / (2 : ℝ) ^ (taoSection5DescentQ B + 1) <
      (B : ℝ) ^ (-(1 / 50 : ℝ)) := by
  let q := taoSection5DescentQ B
  have hnat : B < 2 ^ (50 * (q + 1)) :=
    (threshold_lt_two_pow_log_succ B).trans_le
      (by simpa only [q] using two_pow_log_succ_le_descentQ_bound B)
  have hreal : (B : ℝ) < (2 : ℝ) ^ (50 * (q + 1) : ℕ) := by
    exact_mod_cast hnat
  have hneg := Real.rpow_lt_rpow_of_neg
    (by exact_mod_cast hB : 0 < (B : ℝ)) hreal
    (by norm_num : -(1 / 50 : ℝ) < 0)
  calc
    (1 : ℝ) / (2 : ℝ) ^ (taoSection5DescentQ B + 1) =
        ((2 : ℝ) ^ (taoSection5DescentQ B + 1 : ℕ))⁻¹ := by
      simp only [one_div]
    _ = ((2 : ℝ) ^
        ((taoSection5DescentQ B + 1 : ℕ) : ℝ))⁻¹ :=
      congrArg Inv.inv
        (Real.rpow_natCast (2 : ℝ) (taoSection5DescentQ B + 1)).symm
    _ = (2 : ℝ) ^
        (-((taoSection5DescentQ B + 1 : ℕ) : ℝ)) :=
      (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
    _ = ((2 : ℝ) ^ (50 * (q + 1) : ℕ)) ^ (-(1 / 50 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [q]
      congr 1
      push_cast
      ring
    _ < (B : ℝ) ^ (-(1 / 50 : ℝ)) := hneg

theorem five_mul_descentE_le_log (B : ℕ) :
    5 * taoSection5DescentE B ≤ Nat.log 2 B := by
  have hnDecomp := Nat.div_add_mod (Nat.log 2 B) 10
  have hn0Decomp := Nat.div_add_mod (taoSection5N0 B) 5
  have hlogRem := Nat.mod_lt (Nat.log 2 B) (by norm_num : 0 < 10)
  have hn0Rem := Nat.mod_lt (taoSection5N0 B) (by norm_num : 0 < 5)
  unfold taoSection5DescentE taoSection5DescentQ taoSection5N0
  omega

theorem eventually_five_le_taoSection5N0 :
    ∀ᶠ B : ℕ in atTop, 5 ≤ taoSection5N0 B := by
  filter_upwards [eventually_ge_atTop (2 ^ 50 : ℕ)] with B hB
  have hlog : 50 ≤ Nat.log 2 B :=
    Nat.le_log_of_pow_le (by norm_num) hB
  unfold taoSection5N0
  omega

/-- A logarithmic power budget converts the additive `3^n` term to a
one-fifth power of the threshold. -/
theorem three_pow_le_threshold_rpow_one_fifth_of_mul_le_log
    {B n : ℕ} (hB : 1 ≤ B) (hlog : 10 * n ≤ Nat.log 2 B) :
    (3 : ℝ) ^ n ≤ (B : ℝ) ^ (1 / 5 : ℝ) := by
  have hpowB : 2 ^ (10 * n) ≤ B :=
    Nat.pow_le_of_le_log (Nat.ne_of_gt hB) hlog
  have hpowerNat : ((3 ^ n) ^ 5 : ℕ) ≤ 2 ^ (10 * n) := by
    calc
      ((3 ^ n) ^ 5 : ℕ) = (3 ^ 5) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (2 ^ 10) ^ n :=
        Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ^ 5 ≤ 2 ^ 10) n
      _ = 2 ^ (10 * n) := by rw [pow_mul]
  have hpowerReal : ((3 : ℝ) ^ n) ^ 5 ≤ (B : ℝ) := by
    exact_mod_cast hpowerNat.trans hpowB
  have hrpow : ((3 : ℝ) ^ n) ^ (5 : ℝ) ≤ (B : ℝ) := by
    calc
      ((3 : ℝ) ^ n) ^ (5 : ℝ) = ((3 : ℝ) ^ n) ^ (5 : ℕ) :=
        Real.rpow_natCast ((3 : ℝ) ^ n) 5
      _ ≤ (B : ℝ) := hpowerReal
  simpa [one_div] using
    (Real.le_rpow_inv_iff_of_pos
      (by positivity : 0 ≤ (3 : ℝ) ^ n)
      (by positivity : 0 ≤ (B : ℝ))
      (by norm_num : 0 < (5 : ℝ))).2 hrpow

/-- Scheduled specialization of the additive one-fifth-power estimate. -/
theorem taoSection5_three_pow_n0_le_threshold_rpow_one_fifth
    {B : ℕ} (hB : 1 ≤ B) :
    (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) ^ (1 / 5 : ℝ) := by
  apply three_pow_le_threshold_rpow_one_fifth_of_mul_le_log hB
  unfold taoSection5N0
  omega

/-- Real form of the five-step coefficient gain at the scheduled scale. -/
private theorem rat_three_pow_div_two_pow_lt_threshold_rpow_neg_one_fiftieth
    {B w : ℕ} (hB : 1 ≤ B) (hn0 : 5 ≤ taoSection5N0 B)
    (hweight : 19 * taoSection5N0 B ≤ 10 * w) :
    (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) <
      (B : ℝ) ^ (-(1 / 50 : ℝ)) := by
  have hrat := three_pow_div_two_pow_le_fiveStep hn0 hweight
  have hcast :
      (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) ≤
        (((1 : ℚ) / (2 : ℚ) ^ (taoSection5N0 B / 5 + 1) : ℚ) : ℝ) :=
    Rat.cast_le.mpr hrat
  have hreal :
      (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) ≤
        (1 : ℝ) / (2 : ℝ) ^ (taoSection5N0 B / 5 + 1) := by
    norm_num only [Rat.cast_div, Rat.cast_pow] at hcast ⊢
    exact hcast
  exact hreal.trans_lt
    (by simpa only [taoSection5DescentQ] using
      one_div_two_pow_descentQ_succ_lt_rpow_neg_one_fiftieth hB)

/-- Exact upper real exponent of each scheduled source branch after applying
the window's outer `taoAlpha` power. -/
theorem taoSection5SourceY_rpow_alpha_eq
    (B : ℕ) (branch : TaoSection5SourceBranch) :
    (taoSection5SourceY B branch) ^ taoAlpha =
      (B : ℝ) ^ (match branch with
        | .alpha => taoAlpha ^ 2
        | .alphaSq => taoAlpha ^ 3) := by
  cases branch with
  | alpha =>
      calc
        ((B : ℝ) ^ taoAlpha) ^ taoAlpha =
            (B : ℝ) ^ (taoAlpha * taoAlpha) :=
          (Real.rpow_mul (Nat.cast_nonneg B) taoAlpha taoAlpha).symm
        _ = (B : ℝ) ^ (taoAlpha ^ 2) := by ring_nf
  | alphaSq =>
      calc
        ((B : ℝ) ^ (taoAlpha ^ 2)) ^ taoAlpha =
            (B : ℝ) ^ ((taoAlpha ^ 2) * taoAlpha) :=
          (Real.rpow_mul (Nat.cast_nonneg B) (taoAlpha ^ 2) taoAlpha).symm
        _ = (B : ℝ) ^ (taoAlpha ^ 3) := by ring_nf

/-- Membership in a scheduled odd window gives the exact branch-specific
real-power upper bound. -/
theorem mem_taoSection5SourceWindow_le_branch_rpow
    {B N : ℕ} {branch : TaoSection5SourceBranch}
    (hmem : N ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    (N : ℝ) ≤ (B : ℝ) ^ (match branch with
      | .alpha => taoAlpha ^ 2
      | .alphaSq => taoAlpha ^ 3) := by
  have hmem' :
      N ∈ taoNyOddWindow (taoSection5SourceY B branch) taoAlpha := hmem
  have hYnonneg : 0 ≤ taoSection5SourceY B branch := by
    cases branch <;> exact Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hupper := (taoNyOddWindow_mem hYnonneg).mp hmem'
  rw [taoSection5SourceY_rpow_alpha_eq] at hupper
  exact hupper.2.1

/-- The `alphaSq` branch is the worst branch, with common exponent
`taoAlpha^3`; the first branch is weakened only for bases at least one. -/
theorem mem_taoSection5SourceWindow_le_alpha_cube
    {B N : ℕ} (hB : 1 ≤ B) {branch : TaoSection5SourceBranch}
    (hmem : N ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    (N : ℝ) ≤ (B : ℝ) ^ (taoAlpha ^ 3) := by
  have hbranch := mem_taoSection5SourceWindow_le_branch_rpow hmem
  cases branch with
  | alpha =>
      exact hbranch.trans
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB) (by
          have ha := taoAlpha_one_lt
          nlinarith [sq_nonneg taoAlpha]))
  | alphaSq => exact hbranch

theorem taoAlpha_cube_le_two_hundred_fifty_one_div_two_hundred_fifty :
    taoAlpha ^ 3 ≤ (251 / 250 : ℝ) := by
  norm_num [taoAlpha]

/-- The worst source exponent leaves more than the `1/50` power margin
needed by the five-step quotient. -/
theorem taoAlpha_cube_sub_one_fiftieth_lt :
    taoAlpha ^ 3 - (1 / 50 : ℝ) < 99 / 100 := by
  norm_num [taoAlpha]

/-- The high-weight five-step coefficient times any scheduled source value is
bounded by the main `B^(99/100)` descent term. -/
theorem taoSection5_main_term_le_threshold_rpow_ninety_nine_hundredths
    {B N w : ℕ} (hB : 1 ≤ B) (hn0 : 5 ≤ taoSection5N0 B)
    (hweight : 19 * taoSection5N0 B ≤ 10 * w)
    {branch : TaoSection5SourceBranch}
    (hmem : N ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) * (N : ℝ) ≤
      (B : ℝ) ^ (99 / 100 : ℝ) := by
  have hcoeff :=
    (rat_three_pow_div_two_pow_lt_threshold_rpow_neg_one_fiftieth
      hB hn0 hweight).le
  have hsource := mem_taoSection5SourceWindow_le_alpha_cube hB hmem
  have hproduct :
      (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) * (N : ℝ) ≤
        (B : ℝ) ^ (-(1 / 50 : ℝ)) * (B : ℝ) ^ (taoAlpha ^ 3) :=
    mul_le_mul hcoeff hsource (Nat.cast_nonneg N)
      (Real.rpow_nonneg (Nat.cast_nonneg B) _)
  calc
    (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) * (N : ℝ) ≤
        (B : ℝ) ^ (-(1 / 50 : ℝ)) * (B : ℝ) ^ (taoAlpha ^ 3) :=
      hproduct
    _ = (B : ℝ) ^ (taoAlpha ^ 3 - (1 / 50 : ℝ)) := by
      rw [← Real.rpow_add (by exact_mod_cast hB : 0 < (B : ℝ))]
      congr 1
      ring
    _ ≤ (B : ℝ) ^ (99 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB)
        taoAlpha_cube_sub_one_fiftieth_lt.le

/-- The two sublinear powers in the deterministic descent estimate are
eventually absorbed by the ambient threshold. -/
theorem eventually_taoSection5_descent_absorption :
    ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ (99 / 100 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) ≤ (B : ℝ) := by
  have hfirst :
      Tendsto
        (fun B : ℕ => (B : ℝ) ^ (99 / 100 : ℝ) / (B : ℝ))
        atTop (𝓝 0) := by
    refine
      ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 100 : ℝ))).comp
        tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
    have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
    change
      (B : ℝ) ^ (-(1 / 100 : ℝ)) =
        (B : ℝ) ^ (99 / 100 : ℝ) / (B : ℝ)
    calc
      (B : ℝ) ^ (-(1 / 100 : ℝ)) =
          (B : ℝ) ^ ((99 / 100 : ℝ) - 1) := by norm_num
      _ = (B : ℝ) ^ (99 / 100 : ℝ) / (B : ℝ) ^ (1 : ℝ) :=
        Real.rpow_sub hBpos (99 / 100 : ℝ) 1
      _ = (B : ℝ) ^ (99 / 100 : ℝ) / (B : ℝ) := by
        rw [Real.rpow_one]
  have hsecond :
      Tendsto
        (fun B : ℕ => (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ))
        atTop (𝓝 0) := by
    refine
      ((tendsto_rpow_neg_atTop (by norm_num : 0 < (4 / 5 : ℝ))).comp
        tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
    have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
    change
      (B : ℝ) ^ (-(4 / 5 : ℝ)) =
        (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ)
    calc
      (B : ℝ) ^ (-(4 / 5 : ℝ)) =
          (B : ℝ) ^ ((1 / 5 : ℝ) - 1) := by norm_num
      _ = (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ) ^ (1 : ℝ) :=
        Real.rpow_sub hBpos (1 / 5 : ℝ) 1
      _ = (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ) := by
        rw [Real.rpow_one]
  have hnormalized :
      Tendsto
        (fun B : ℕ =>
          (B : ℝ) ^ (99 / 100 : ℝ) / (B : ℝ) +
            (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ))
        atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  filter_upwards
    [hnormalized.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (0 : ℕ)] with B hbound hB
  have hB0 : (B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hB)
  have hmul := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg B)
  calc
    (B : ℝ) ^ (99 / 100 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) =
        ((B : ℝ) ^ (99 / 100 : ℝ) / (B : ℝ) +
          (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ)) * (B : ℝ) := by
      field_simp [hB0]
    _ ≤ 1 * (B : ℝ) := hmul
    _ = (B : ℝ) := one_mul _

/-- Eventual scale data consumed by deterministic Section 5 descent. -/
structure TaoSection5DescentScaleFacts (B : ℕ) : Prop where
  one_le_B : 1 ≤ B
  five_le_n0 : 5 ≤ taoSection5N0 B
  absorption :
    (B : ℝ) ^ (99 / 100 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) ≤ (B : ℝ)

theorem eventually_taoSection5DescentScaleFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5DescentScaleFacts B := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_five_le_taoSection5N0,
    eventually_taoSection5_descent_absorption] with B hB hn0 habsorb
  exact
    { one_le_B := hB
      five_le_n0 := hn0
      absorption := habsorb }

theorem TaoSection5DescentScaleFacts.main_term
    {B N w : ℕ} (facts : TaoSection5DescentScaleFacts B)
    (hweight : 19 * taoSection5N0 B ≤ 10 * w)
    {branch : TaoSection5SourceBranch}
    (hmem : N ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch)) :
    (((3 : ℚ) ^ taoSection5N0 B / (2 : ℚ) ^ w : ℚ) : ℝ) * (N : ℝ) ≤
      (B : ℝ) ^ (99 / 100 : ℝ) :=
  taoSection5_main_term_le_threshold_rpow_ninety_nine_hundredths
    facts.one_le_B facts.five_le_n0 hweight hmem

theorem TaoSection5DescentScaleFacts.offset
    {B : ℕ} (facts : TaoSection5DescentScaleFacts B) :
    (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) ^ (1 / 5 : ℝ) :=
  taoSection5_three_pow_n0_le_threshold_rpow_one_fifth facts.one_le_B

end Tao
end Erdos1135
