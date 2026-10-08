/-
Compatibility modification, 8 October 2026: proof elaboration and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitConductor

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem forwardGoodDepthShiftUnitMass_le_two_conductor_of_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K m k : ℕ) (hmk : m ≤ k)
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ t : ℕ, (Tao.syracuse^[t]) (U.state.root i) = 1)
    (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ k : ℕ) : ℝ) ≤ X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (hsource : ∀ z : (U.forwardIterate cap n).FullTerminalIncidence X hX hi,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hL1 : ndTernaryUniformMean k (fun y => |ndSyracuseUnitReferenceDensity k y -
      ndSyracuseUnitReferenceDensity m (Tao.taoZModThreeProjection hmk y)|) ≤ epsilon)
    (p : ℕ) (hp : 0 < p)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ)*(p:ℝ)) :
    U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi ≤
      (8 / 9 : ℝ) * (p : ℝ) * U.fullGoodCoreTerminalMass cap width n
        ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 +
        44 * U.parentSourcePotential * epsilon := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  apply (U.forwardGoodDepthShiftUnitMass_le_full_cap_one_fan cap width n K k X hX hi).trans
  have h := U.fullTerminal_subweight_fan_two_conductor_bound_of_height cap n (V.fullTerminalShift X hX hi)
    1 (K / 2 + 1) hseedNeOne hseedHitsOne
    (U.fullGoodCoreTerminalWeight cap width n (V.fullTerminalShift X hX hi) 1)
    (U.fullGoodCoreTerminalWeight_nonneg cap width n (V.fullTerminalShift X hX hi) 1)
    (U.fullGoodCoreTerminalWeight_le_original cap width n (V.fullTerminalShift X hX hi) 1)
    m k hmk X hX hQ hsource epsilon he hL1 ((2/3:ℝ)*(p:ℝ)) (by positivity) hheight
  convert h using 1; unfold fullGoodCoreTerminalMass; ring

theorem fullGoodCoreTerminalMass_ge_of_square_budget_and_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K m k : ℕ)
    (hm : 1 ≤ m) (hmk : m ≤ k) (hk : k ≤ (U.forwardIterate cap n).floor)
    {Cclock Cmix a : ℝ} (hCclock : 250 ≤ Cclock)
    (htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet Cclock)
    (hCmix : 0 ≤ Cmix) (hmix : ndExplicitQuadraticMixingAt Cmix m)
    (ha : 0 < a) (hsquare : 88 * U.parentSourcePotential * Cmix ≤ a * (m : ℝ) ^ 2)
    (p : ℕ) (hp : 0 < p)
    (hheight : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ)*(p:ℝ))
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (hmark : a ≤ U.forwardCoreTerminalGoodDepthShiftUnitMass cap width n K k X hX hi) :
    9 * a / (16 * (p : ℝ)) ≤ U.fullGoodCoreTerminalMass cap width n
      ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 := by
  let V := U.forwardIterate cap n
  have hOrig := (ha.trans_le hmark).trans_le
    (U.forwardGoodDepthShiftUnitMass_le_original cap width n K k X hX hi)
  have hQ := U.terminal_conductor_room_of_pos_mark cap width n K k hk X hX hi hOrig
  have ht : ∀ i, V.state.root i ∈ oddSyracuseLogTimeOneSet Cclock := by
    dsimp [V]
    rw [U.forwardIterate_eq_iterate cap n]
    exact U.iterate_root_mem_same_target cap hCclock htarget n
  have hn : ∀ i, U.state.root i ≠ 1 := by
    intro i
    have hl := (Nat.pow_le_pow_right (by norm_num : 1 ≤ 16)
      (show 1 ≤ U.state.base i by have := U.floor_le_base i; have := U.floor_twoHundred; omega)).trans
      (U.state.rootLower i)
    norm_num at hl
    omega
  have hh : ∀ i, ∃ t : ℕ, (Tao.syracuse^[t]) (U.state.root i) = 1 := by
    intro i
    obtain ⟨_, _, t, _, ht⟩ := htarget i
    exact ⟨t, ht⟩
  have hbound := U.forwardGoodDepthShiftUnitMass_le_two_conductor_of_height cap width n K m k hmk
    hn hh X hX hQ.le hi
    (fun z => (V.fullTerminal_source_mem_target_and_window X hX hi hCclock ht z).2)
    (Cmix / (m : ℝ) ^ 2) (div_nonneg hCmix (by positivity)) (hmix k hmk) p hp hheight
  have herror := explicitConductor_error_le_half hm hsquare
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (p : ℝ))).2
  nlinarith only [hmark, hbound, herror]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
