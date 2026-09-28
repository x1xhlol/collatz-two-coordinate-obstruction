/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreVariation
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceMarkedPhysicalIncidence
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators Topology

open Filter

noncomputable section

def ndRootCoreWidth (b : ℕ) : ℕ := ⌈(b : ℝ) ^ (3 / 5 : ℝ)⌉₊

theorem rootCoreWidth_lower (b : ℕ) :
    (b : ℝ) ^ (3 / 5 : ℝ) ≤ (ndRootCoreWidth b : ℝ) := Nat.le_ceil _

theorem rootCoreWidth_upper {b : ℕ} (hb : 1 ≤ b) :
    (ndRootCoreWidth b : ℝ) ≤ 2 * (b : ℝ) ^ (3 / 5 : ℝ) := by
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg b) (3 / 5 : ℝ))
  have hp : 1 ≤ (b : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hb) (by norm_num)
  change (ndRootCoreWidth b : ℝ) < _ at h
  linarith

theorem rootCoreWidth_guard {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    16 ≤ ndRootCoreWidth b ∧ ndRootCoreWidth b ≤ ndGeom2ShiftedWideSymmetricWidth b := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hb32 : (32 : ℝ) ^ 5 ≤ b := by exact_mod_cast hb
  have h3 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 32 ^ 5) hb32 (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have h2 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 32 ^ 5) hb32 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 32)] at h3 h2
  norm_num at h3 h2
  have hprod : (b : ℝ) ^ (3 / 5 : ℝ) * (b : ℝ) ^ (2 / 5 : ℝ) = b := by
    rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < b))]
    norm_num
  have hp := Real.rpow_nonneg hb0 (3 / 5 : ℝ)
  have hhalf : 2 * (b : ℝ) ^ (3 / 5 : ℝ) ≤ b := by nlinarith
  have hceil := Nat.ceil_lt_add_one hp
  have hlo := rootCoreWidth_lower b
  change (ndRootCoreWidth b : ℝ) < _ at hceil
  have hnat : 2 * ndRootCoreWidth b < b + 2 := by
    exact_mod_cast (show 2 * (ndRootCoreWidth b : ℝ) < (b : ℝ) + 2 by linarith)
  constructor
  · exact_mod_cast (show (16 : ℝ) ≤ ndRootCoreWidth b by linarith)
  · unfold ndGeom2ShiftedWideSymmetricWidth
    omega

def ndRootCoreGrowth : ℝ := 2013 / 2000

theorem rootCoreGrowth_ge_one : 1 ≤ ndRootCoreGrowth := by norm_num [ndRootCoreGrowth]

theorem rootCore_fractional_growth_le :
    (101 / 100 : ℝ) ^ (3 / 5 : ℝ) ≤ ndRootCoreGrowth := by
  have hp : ((101 / 100 : ℝ) ^ (3 / 5 : ℝ)) ^ 5 = (101 / 100 : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  by_contra hn
  have hh := pow_lt_pow_left₀ (lt_of_not_ge hn) (by norm_num [ndRootCoreGrowth]) (by decide : 5 ≠ 0)
  rw [hp] at hh
  norm_num [ndRootCoreGrowth] at hh

theorem rootCore_mixing_ratio_lt_one :
    ndRootCoreGrowth * (200 / 201 : ℝ) ^ 6 < 1 := by norm_num [ndRootCoreGrowth]

theorem rootCore_cap_ratio_lt_one :
    ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ) < 1 := by
  have he : ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ 100 = (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hp : (ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ 100 < 1 := by
    rw [mul_pow, he]
    norm_num [ndRootCoreGrowth]
  by_contra hn
  have hh : 1 ≤ (ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ 100 :=
    one_le_pow₀ (le_of_not_gt hn)
  linarith

theorem rootCore_strip_failure_le_inverse_sixth {b : ℕ} (hb : 1 ≤ b) :
    (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) ≤
      (8 * (Nat.factorial 35 : ℝ) * 576 ^ 35) / (b : ℝ) ^ 6 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  let x : ℝ := (b : ℝ) ^ (1 / 5 : ℝ) / 576
  have hx : 0 < x := by dsimp [x]; positivity
  have hsquare : ((b : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = (b : ℝ) ^ (1 / 5 : ℝ) * b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    have he := Real.rpow_add hb0 (1 / 5 : ℝ) 1
    norm_num at he ⊢
    exact he
  have hlo := rootCoreWidth_lower b
  have hq : x ≤ (ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hb0.le _) hlo 2
    rw [hsquare] at hh
    dsimp [x]
    nlinarith
  have ht := Real.pow_div_factorial_le_exp x hx.le 35
  have hfac : (0 : ℝ) < Nat.factorial 35 := by positivity
  have hexp : Real.exp (-x) ≤ (Nat.factorial 35 : ℝ) / x ^ 35 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hx _)).mpr
    rw [one_mul]
    rw [mul_comm]
    exact (div_le_iff₀ hfac).mp ht
  have hp : x ^ 35 = (b : ℝ) ^ 7 / 576 ^ 35 := by
    dsimp [x]
    rw [div_pow, ← Real.rpow_mul_natCast hb0.le]
    norm_num
  calc
    _ ≤ (4 * (b : ℝ) + 4) * Real.exp (-x) := by gcongr
    _ ≤ (8 * (b : ℝ)) * ((Nat.factorial 35 : ℝ) / x ^ 35) := by gcongr; linarith
    _ = _ := by rw [hp]; field_simp

theorem rootCoreCapSum_eq_sum (cap : ℕ → ℕ) (n : ℕ) :
    ndRootCoreCapSum cap n = ∑ j ∈ Finset.range n, cap j := by
  induction n generalizing cap with
  | zero => simp [ndRootCoreCapSum]
  | succ n ih =>
      rw [ndRootCoreCapSum, ih, Finset.sum_range_succ']
      exact add_comm _ _

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem core_forward_floor_geometric_lower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    (U.floor : ℝ) * (201 / 200 : ℝ) ^ n ≤ ((U.forwardIterate cap n).floor : ℝ) := by
  have h := U.geometricIntervalStoppedIterate_real_floor_lower cap 0 n
  rw [U.geometricIntervalStoppedIterate_floor_eq_iterate] at h
  simpa only [U.forwardIterate_eq_iterate] using h

theorem core_forward_floor_geometric_upper
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    ((U.forwardIterate cap n).floor : ℝ) ≤ (U.floor : ℝ) * (101 / 100 : ℝ) ^ n := by
  induction n with
  | zero => simp [forwardIterate]
  | succ n ih =>
      rw [U.forwardIterate_succ_eq_next cap n]
      change (((U.forwardIterate cap n).floor + (U.forwardIterate cap n).floor / 100 : ℕ) : ℝ) ≤ _
      have hd : (((U.forwardIterate cap n).floor / 100 : ℕ) : ℝ) * 100 ≤
          (U.forwardIterate cap n).floor := by
        exact_mod_cast Nat.div_mul_le_self (U.forwardIterate cap n).floor 100
      push_cast
      rw [pow_succ]
      nlinarith

theorem coreWidthSum_eq_sum
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ) :
    U.coreWidthSum cap width n = ∑ j ∈ Finset.range n, width (U.forwardIterate cap j).floor := by
  induction n generalizing U cap with
  | zero => simp [coreWidthSum]
  | succ n ih =>
      rw [coreWidthSum, ih, Finset.sum_range_succ']
      exact add_comm _ _

theorem coreWidth_at_forward_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    (ndRootCoreWidth (U.forwardIterate cap n).floor : ℝ) ≤
      2 * (U.floor : ℝ) ^ (3 / 5 : ℝ) * ndRootCoreGrowth ^ n := by
  have h := rootCoreWidth_upper (b := (U.forwardIterate cap n).floor)
    (by have hh := (U.forwardIterate cap n).floor_twoHundred; omega)
  have hg := Real.rpow_le_rpow (Nat.cast_nonneg _) (U.core_forward_floor_geometric_upper cap n)
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num), mul_comm (n : ℝ),
    Real.rpow_mul_natCast (by norm_num)] at hg
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 101 / 100) _)
    rootCore_fractional_growth_le n
  calc
    _ ≤ 2 * (U.floor : ℝ) ^ (3 / 5 : ℝ) * ((101 / 100 : ℝ) ^ (3 / 5 : ℝ)) ^ n := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem coreWidthSum_le_geometric
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    (U.coreWidthSum cap ndRootCoreWidth n : ℝ) ≤
      2 * (U.floor : ℝ) ^ (3 / 5 : ℝ) * (n : ℝ) * ndRootCoreGrowth ^ n := by
  rw [U.coreWidthSum_eq_sum]
  push_cast
  calc
    _ ≤ ∑ _j ∈ Finset.range n, 2 * (U.floor : ℝ) ^ (3 / 5 : ℝ) * ndRootCoreGrowth ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      exact (U.coreWidth_at_forward_le cap j).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ rootCoreGrowth_ge_one
          (Finset.mem_range.mp hj).le) (by positivity))
    _ = _ := by simp; ring

theorem coreCapacityBudget_le_geometric
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (L : ℕ) (hc : ∀ n, cap n ≤ L * (n + 1)) (n : ℕ) :
    U.coreCapacityBudget cap ndRootCoreWidth n ≤
      U.denominator * ((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
        ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor)) *
      ((n + 1 : ℕ) : ℝ) ^ 3 * ndRootCoreGrowth ^ n := by
  have hw := U.coreWidthSum_le_geometric cap n
  have hk : ndRootCoreCapSum cap n ≤ L * (n + 1) ^ 2 := by
    rw [rootCoreCapSum_eq_sum]
    calc
      _ ≤ ∑ _j ∈ Finset.range n, L * (n + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hc j).trans (Nat.mul_le_mul_left L (by have h := Finset.mem_range.mp hj; omega))
      _ ≤ _ := by simp; nlinarith
  have hkr : ((ndRootCoreCapSum cap n + 4 * n + 1 : ℕ) : ℝ) ≤
      (L + 5 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h : (ndRootCoreCapSum cap n : ℝ) ≤ (L : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hk
    push_cast at h ⊢
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hr : 1 ≤ ndRootCoreGrowth ^ n := one_le_pow₀ rootCoreGrowth_ge_one
  have hwr : ((2 * U.coreWidthSum cap ndRootCoreWidth n + 1 : ℕ) : ℝ) ≤
      (4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * ndRootCoreGrowth ^ n := by
    have hp := Real.rpow_nonneg (Nat.cast_nonneg U.floor) (3 / 5 : ℝ)
    have hn := Nat.cast_nonneg (α := ℝ) n
    push_cast
    nlinarith
  have he : (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hD : 0 ≤ U.denominator := by
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  unfold coreCapacityBudget
  push_cast
  calc
    _ ≤ U.denominator *
        (((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) * ndRootCoreGrowth ^ n) *
        ((L + 5 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)) *
        ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hD
        exact mul_le_mul (by simpa using hwr) (by simpa using hkr)
          (by positivity) (by positivity)
      · exact add_le_add_right (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 16 ^ U.floor)) _
      · positivity
      · positivity
    _ = _ := by push_cast; ring

theorem core_inverse_floor_le_geometric
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    1 / ((U.forwardIterate cap n).floor : ℝ) ≤
      (1 / (U.floor : ℝ)) * (200 / 201 : ℝ) ^ n := by
  have hseed : (0 : ℝ) < U.floor := by exact_mod_cast (by have h := U.floor_twoHundred; omega : 0 < U.floor)
  calc
    _ ≤ 1 / ((U.floor : ℝ) * (201 / 200 : ℝ) ^ n) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (U.core_forward_floor_geometric_lower cap n)
    _ = _ := by
      rw [div_mul_eq_div_div, div_eq_mul_inv _ ((201 / 200 : ℝ) ^ n), ← inv_pow]
      norm_num

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem rootCore_cap_failure_le_geometric
    (cap : ℕ → ℕ) (K0 : ℕ) (hc : ∀ n, K0 + n / 100 ≤ cap n) (n : ℕ) :
    (1 / 2 : ℝ) ^ (cap n + 1) ≤
      (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by
  have hn : 100 * K0 + n ≤ 100 * (cap n + 1) := by have h := hc n; omega
  have he : (K0 : ℝ) + (n : ℝ) / 100 ≤ ((cap n + 1 : ℕ) : ℝ) := by
    have hh : 100 * (K0 : ℝ) + (n : ℝ) ≤ 100 * ((cap n + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  calc
    _ = (1 / 2 : ℝ) ^ (((cap n + 1 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
    _ ≤ (1 / 2 : ℝ) ^ ((K0 : ℝ) + (n : ℝ) / 100) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) he
    _ = _ := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
      rw [show (n : ℝ) / 100 = (1 / 100 : ℝ) * n by ring,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]

def ndRootCoreStripConstant : ℝ := 8 * (Nat.factorial 35 : ℝ) * 576 ^ 35

theorem rootCore_quarter_error_le {b : ℕ} (hb : 200 ≤ b) {C : ℝ} (hC : 0 ≤ C) :
    C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
      (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) ≤
      (2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hk0 : (0 : ℝ) < ((b / 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < b / 4)
  have hb8 : (b : ℝ) ≤ 8 * ((b / 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : b ≤ 8 * (b / 4))
  have hrec : 1 / ((b / 4 : ℕ) : ℝ) ≤ 8 / (b : ℝ) := by
    exact (div_le_div_iff₀ hk0 hb0).mpr (by simpa only [one_mul] using hb8)
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / ((b / 4 : ℕ) : ℝ)) hrec 6
  have hpow : C / ((b / 4 : ℕ) : ℝ) ^ 6 ≤ C * (8 / (b : ℝ)) ^ 6 := by
    simpa only [div_pow, one_pow, mul_one_div] using mul_le_mul_of_nonneg_left hp hC
  have hn : C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 ≤ C / ((b / 4 : ℕ) : ℝ) ^ 6 := by
    apply div_le_div_of_nonneg_left hC (pow_pos hk0 _)
    apply pow_le_pow_left₀ hk0.le
    exact_mod_cast (by omega : b / 4 ≤ (b + b / 100) / 4)
  have he := rootCore_strip_failure_le_inverse_sixth (b := b) (by omega)
  change _ ≤ ndRootCoreStripConstant / (b : ℝ) ^ 6 at he
  calc
    _ ≤ 2 * (C * (8 / (b : ℝ)) ^ 6) + ndRootCoreStripConstant / (b : ℝ) ^ 6 := by linarith
    _ = _ := by rw [div_pow]; ring

def ndRootCoreVariationMajorant (b L K0 : ℕ) (C : ℝ) (n : ℕ) : ℝ :=
  ((4 * (b : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
    ((2 : ℝ) ^ (b + 1) + (16 : ℝ) ^ b)) * (2 / 3 : ℝ) *
    ((n + 1 : ℕ) : ℝ) ^ 3 *
    (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6) *
      (ndRootCoreGrowth * (200 / 201 : ℝ) ^ 6) ^ n +
      (1 / 2 : ℝ) ^ K0 * (ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n)

theorem rootCoreVariationMajorant_nonneg (b L K0 n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ ndRootCoreVariationMajorant b L K0 C n := by
  unfold ndRootCoreVariationMajorant ndRootCoreStripConstant ndRootCoreGrowth
  positivity

private theorem summable_core_succ_cube_geometric {r : ℝ} (hr : |r| < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 3 * r ^ n) := by
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 (by simpa using hr : ‖r‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by simpa using hr : ‖r‖ < 1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hr : ‖r‖ < 1)
  have h0 := summable_geometric_of_norm_lt_one (by simpa using hr : ‖r‖ < 1)
  convert ((h3.add (h2.mul_left 3)).add (h1.mul_left 3)).add h0 using 1
  ext n
  push_cast
  ring

theorem summable_rootCoreVariationMajorant (b L K0 : ℕ) (C : ℝ) :
    Summable (ndRootCoreVariationMajorant b L K0 C) := by
  have hm := summable_core_succ_cube_geometric (r := ndRootCoreGrowth * (200 / 201 : ℝ) ^ 6)
    (by rw [abs_of_nonneg (by norm_num [ndRootCoreGrowth])]; exact rootCore_mixing_ratio_lt_one)
  have hc := summable_core_succ_cube_geometric (r := ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ))
    (by rw [abs_of_nonneg (by unfold ndRootCoreGrowth; positivity)]; exact rootCore_cap_ratio_lt_one)
  convert ((hm.mul_left ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6)).add
    (hc.mul_left ((1 / 2 : ℝ) ^ K0))).mul_left
    (((4 * (b : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
      ((2 : ℝ) ^ (b + 1) + (16 : ℝ) ^ b)) * (2 / 3 : ℝ)) using 1
  ext n
  unfold ndRootCoreVariationMajorant
  ring

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem forward_core_width_guard
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 32 ^ 5 ≤ U.floor)
    (cap : ℕ → ℕ) (n : ℕ) :
    16 ≤ ndRootCoreWidth (U.forwardIterate cap n).floor ∧
      ndRootCoreWidth (U.forwardIterate cap n).floor ≤ ndGeom2ShiftedWideSymmetricWidth (U.forwardIterate cap n).floor := by
  apply rootCoreWidth_guard
  have hg := U.core_forward_floor_geometric_lower cap n
  have hp : 1 ≤ (201 / 200 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hle : (U.floor : ℝ) ≤ (U.forwardIterate cap n).floor := by
    nlinarith [Nat.cast_nonneg (α := ℝ) U.floor]
  exact hb.trans (by exact_mod_cast hle)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def ndRootCoreVariationTail (b L K0 : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, ndRootCoreVariationMajorant b L K0 C (N + j)

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem rootCoreProbabilityProduct_eq_prod_forward
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap width : ℕ → ℕ) (n : ℕ) :
    ndRootCoreProbabilityProduct U.floor cap width n =
      ∏ j ∈ Finset.range n, ndRootCoreStripBoundedCrossingProbability
        (U.forwardIterate cap j).floor (width (U.forwardIterate cap j).floor) (cap j) := by
  induction n generalizing U cap with
  | zero => simp [ndRootCoreProbabilityProduct]
  | succ n ih =>
      change _ * ndRootCoreProbabilityProduct (U.next (cap 0)).floor _ width n = _
      rw [ih, Finset.prod_range_succ']
      exact mul_comm _ _

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
