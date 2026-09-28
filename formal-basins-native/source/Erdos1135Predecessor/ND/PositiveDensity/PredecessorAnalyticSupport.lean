/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

/-
Copyright (c) 2026 Lech Mazur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Erdos1135Predecessor.ND.PositiveDensity.A5HistoricalAdjacentCylinderPreviousPhysicalLowerShellNoGo
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitConductor
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricOutwardBaseGrowth
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceDensityTransport
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideGeometricSynchronizedIntervals

/-! Analytic estimates used by the general-target predecessor theorem. -/

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem self_le_ndA5PreviousPhysicalCollapseSource (m : ℕ) :
    m ≤ ndA5PreviousPhysicalCollapseSource m := by
  induction m with
  | zero => simp [ndA5PreviousPhysicalCollapseSource]
  | succ m ih =>
      rw [ndA5PreviousPhysicalCollapseSource_succ]
      omega

theorem unitReferenceDensity_finite_upper (m : ℕ) (y : ZMod (3 ^ m)) :
    ndSyracuseUnitReferenceDensity m y ≤ (2 / 3 : ℝ) * ((3 ^ m : ℕ) : ℝ) := by
  have h := Finset.single_le_sum (f := ndSyracuseUnitReferenceDensity m)
    (fun z _ => ndSyracuseUnitReferenceDensity_nonneg m z) (Finset.mem_univ y)
  have hm := unitReferenceDensity_fullMean_eq m
  unfold ndTernaryUniformMean ndTernaryUniformScale at hm
  have hsum : (∑ z, ndSyracuseUnitReferenceDensity m z) =
      (2 / 3 : ℝ) * ((3 ^ m : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < ((3 ^ m : ℕ) : ℝ) := by positivity
    field_simp at hm
    nlinarith
  exact h.trans_eq hsum

theorem explicitMixing_quadratic {C : ℝ} (hC : 0 ≤ C)
    (hmix : Tao.syracFineScaleMixingAt 6 C) {m : ℕ} (hm : 1 ≤ m) :
    ndExplicitQuadraticMixingAt C m := by
  intro k hmk
  rw [unitReferenceDensity_fullL1_eq_twoThirds_oscillation hmk]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 6 :=
    pow_le_pow_right₀ hmR (by decide)
  calc
    _ ≤ (2 / 3 : ℝ) * (C / (m : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left (hmix k m hm hmk) (by norm_num)
    _ ≤ C / (m : ℝ) ^ 6 := mul_le_of_le_one_left (by positivity) (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left hC (by positivity) hpow

def ndExplicitRootIntervalHeight (b L M N : ℕ) : ℕ :=
  2 ^ ((2 * N + 4) * b * 2 ^ N + N * (L * (N + 1) + 1)) * M

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem explicitConductor_quarter_room
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (m n : ℕ) (hn : 2 * m ≤ n) :
    m ≤ (U.forwardIterate cap n).floor / 4 ∧
      (U.forwardIterate cap n).floor / 4 ≤ (U.forwardIterate cap n).floor := by
  have hf : U.floor + 2 * n ≤ (U.forwardIterate cap n).floor := by
    have h := U.floor_add_two_mul_le_geometricIntervalStoppedIterate_floor cap 0 n
    rw [U.geometricIntervalStoppedIterate_floor_eq_iterate cap 0 n] at h
    simpa only [U.forwardIterate_eq_iterate cap n] using h
  constructor
  · omega
  · exact Nat.div_le_self _ _

theorem iterate_floor_le_explicit_twoPow
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (cap : ℕ → ℕ) (n : ℕ) :
    (U.iterate cap n).floor ≤ U.floor * 2 ^ n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    change (U.iterate cap n).floor + (U.iterate cap n).floor / 100 ≤ _
    have hd := Nat.div_le_self (U.iterate cap n).floor 100
    rw [pow_succ]
    nlinarith

theorem next_root_le_explicit_twoPow
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (K : ℕ) (z : (U.next K).state.Label) :
    (U.next K).state.root z ≤ 2 ^ (K + 1 + 2 * U.floor) *
      U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := by
  have hlower : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
  have h := ndGeom2PredictableRootSideUnitChildIncidence_threePow_mul_source_le_twoPow_capSucc_mul_fourPow_mul_parent
    U.state.root_odd (by have h := U.floor_twoHundred; omega) hlower z
  calc
    _ ≤ 3 ^ U.floor * (U.next K).state.root z := by
      have hp : 1 ≤ 3 ^ U.floor := one_le_pow₀ (by decide)
      simpa only [one_mul] using Nat.mul_le_mul_right ((U.next K).state.root z) hp
    _ ≤ 2 ^ (K + 1) * 4 ^ U.floor *
        U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := h
    _ = _ := by rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_add]

theorem iterate_root_le_explicit_twoPow
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (L M : ℕ) (hcap : ∀ n, cap n ≤ L * (n + 1))
    (hroot : ∀ i, U.state.root i ≤ M) (n : ℕ) :
    ∀ i : (U.iterate cap n).state.Label,
      (U.iterate cap n).state.root i ≤
        2 ^ (n * (L * (n + 1) + 1 + 2 * U.floor * 2 ^ n)) * M := by
  induction n with
  | zero => simpa [iterate] using hroot
  | succ n ih =>
    intro z
    have hf := U.iterate_floor_le_explicit_twoPow cap n
    have hc := hcap n
    have hexp : cap n + 1 + 2 * (U.iterate cap n).floor +
        n * (L * (n + 1) + 1 + 2 * U.floor * 2 ^ n) ≤
        (n + 1) * (L * (n + 1 + 1) + 1 + 2 * U.floor * 2 ^ (n + 1)) := by
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ 2 ^ (cap n + 1 + 2 * (U.iterate cap n).floor) *
          (U.iterate cap n).state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) :=
        (U.iterate cap n).next_root_le_explicit_twoPow (cap n) z
      _ ≤ 2 ^ (cap n + 1 + 2 * (U.iterate cap n).floor) *
          (2 ^ (n * (L * (n + 1) + 1 + 2 * U.floor * 2 ^ n)) * M) :=
        Nat.mul_le_mul_left _ (ih _)
      _ = 2 ^ (cap n + 1 + 2 * (U.iterate cap n).floor +
          n * (L * (n + 1) + 1 + 2 * U.floor * 2 ^ n)) * M := by rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) hexp)

theorem physicalIntervalMax_le_explicit_twoPow {b root : ℕ} (hb : 200 ≤ b) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMax b root ≤ ((2 ^ (4 * b) * root : ℕ) : ℝ) := by
  have hrad := ten_mul_ndGeom2ShiftedWideSymmetricShiftRadius_le_three_mul_add_five hb
  have hr : ndGeom2ShiftedWideSymmetricShiftRadius b ≤ b := by omega
  unfold ndGeom2ShiftedWideSymmetricPhysicalIntervalMax ndGeom2ShiftedWideSymmetricPhysicalLowerScale
  have hden : (1 : ℝ) ≤ ((4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b by
      have hp : 0 < 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b := by positivity
      omega)
  apply le_trans (div_le_self (by positivity) hden)
  exact_mod_cast (show 2 ^ (2 * ndGeom2ShiftedWideSymmetricShiftRadius b) * 4 ^ b * root ≤
      2 ^ (4 * b) * root by
    apply Nat.mul_le_mul_right
    calc
      _ = 2 ^ (2 * ndGeom2ShiftedWideSymmetricShiftRadius b + 2 * b) := by
        rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega))

theorem iterate_physicalIntervalMax_le_explicit
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (L M : ℕ) (hcap : ∀ n, cap n ≤ L * (n + 1))
    (hroot : ∀ i, U.state.root i ≤ M) (n : ℕ) (i : (U.iterate cap n).state.Label) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.iterate cap n).floor
      ((U.iterate cap n).state.root i) ≤
      ((2 ^ ((2 * n + 4) * U.floor * 2 ^ n + n * (L * (n + 1) + 1)) * M : ℕ) : ℝ) := by
  have hf := U.iterate_floor_le_explicit_twoPow cap n
  have hr := U.iterate_root_le_explicit_twoPow cap L M hcap hroot n i
  apply le_trans (physicalIntervalMax_le_explicit_twoPow (U.iterate cap n).floor_twoHundred)
  exact_mod_cast (show 2 ^ (4 * (U.iterate cap n).floor) * (U.iterate cap n).state.root i ≤ _ by
    calc
      _ ≤ 2 ^ (4 * (U.iterate cap n).floor) *
          (2 ^ (n * (L * (n + 1) + 1 + 2 * U.floor * 2 ^ n)) * M) := Nat.mul_le_mul_left _ hr
      _ = 2 ^ (4 * (U.iterate cap n).floor + n * (L * (n + 1) + 1 + 2 * U.floor * 2 ^ n)) * M := by
        rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (by nlinarith)))

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
