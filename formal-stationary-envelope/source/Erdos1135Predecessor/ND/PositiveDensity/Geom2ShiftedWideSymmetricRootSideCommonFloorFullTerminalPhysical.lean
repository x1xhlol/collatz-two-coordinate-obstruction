/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideGeometricSynchronizedIntervals

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

private theorem fullTerminal_power_room {b : ℕ} (hb : 200 ≤ b) :
    4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
      16 ^ (b / 100) ≤ 4 ^ b := by
  have h :=
    four_mul_twoPowShiftRadius_mul_threePow_mul_sixteenPow_base_add_oneHundredth_le_sixtyFourPow hb
  have h' : 16 ^ b *
      (4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * 16 ^ (b / 100)) ≤
      16 ^ b * 4 ^ b := by
    calc
      _ = 4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b *
          16 ^ (b + b / 100) := by rw [pow_add]; ring
      _ ≤ 64 ^ b := h
      _ = _ := by rw [← mul_pow]; norm_num
  exact Nat.le_of_mul_le_mul_left h' (by positivity)

theorem ndGeom2RootSideCommonFloorShifted_sourceLower
    {Label : Type*} {root rootBase shift : Label → ℕ} {b K : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hlower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K) :
    16 ^ (rootBase (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) + b / 100) ≤
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let q := rootBase i
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hpacket : ∀ j, 16 ^ b ≤ root j := fun j =>
    (Nat.pow_le_pow_right (by norm_num) (hfloor j)).trans (hlower j)
  have hshell := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
    hodd (fun _ => by omega) hpacket z
  have hscale : 4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) ≤ 4 ^ b * 16 ^ q := by
    calc
      _ = 16 ^ q * (4 * 2 ^ r * 3 ^ b * 16 ^ (b / 100)) := by
        rw [pow_add]; ring
      _ ≤ 16 ^ q * 4 ^ b := Nat.mul_le_mul_left _ (fullTerminal_power_room hb)
      _ = _ := by ring
  have hnum : 4 ^ b * 16 ^ q ≤ 2 ^ shift i * 4 ^ b * root i := by
    calc
      _ ≤ 4 ^ b * root i := Nat.mul_le_mul_left _ (hlower i)
      _ ≤ 2 ^ shift i * (4 ^ b * root i) := by
        simpa using Nat.mul_le_mul_right (4 ^ b * root i) (Nat.one_le_two_pow (n := shift i))
      _ = _ := by ring
  have hcross : 4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) ≤
      4 * 2 ^ r * 3 ^ b * source := hscale.trans (hnum.trans hshell.1)
  exact Nat.le_of_mul_le_mul_left hcross (by positivity)

theorem ndGeom2RootSideCommonFloorShifted_depth_le_logGap
    {Label : Type*} {root rootBase shift : Label → ℕ} {b K : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hlower : ∀ i, 16 ^ rootBase i ≤ root i)
    (hupper : ∀ i, root i < 16 ^ (rootBase i + 1))
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z : ℝ) ≤
      250 * (Real.log (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) -
        Real.log (root (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) : ℝ)) := by
  exact shiftedWideUniformFloorPhysicalEdgeDepth_cast_le_twoHundredFifty_mul_logGap
    hb
    (ndGeom2ShiftedWideSymmetricSelectedDepth_le_two_mul_add_one
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_depth_mem z))
    (Odd.pos (hodd _)) (hupper _)
    (ndGeom2RootSideCommonFloorShifted_sourceLower hodd hb hfloor hlower z)

theorem ndGeom2RootSideCommonFloorShifted_source_mem_same_target
    {Label : Type*} {root rootBase shift : Label → ℕ} {b K : ℕ} {C : ℝ}
    (hodd : ∀ i, Odd (root i)) (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hlower : ∀ i, 16 ^ rootBase i ≤ root i)
    (hupper : ∀ i, root i < 16 ^ (rootBase i + 1))
    (hC : 250 ≤ C) (htarget : ∀ i, root i ∈ oddSyracuseLogTimeOneSet C)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈
      oddSyracuseLogTimeOneSet C := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let depth := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  have hpacket : ∀ j, 16 ^ b ≤ root j := fun j =>
    (Nat.pow_le_pow_right (by norm_num) (hfloor j)).trans (hlower j)
  have hsourceOdd : Odd source :=
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
      hodd (fun _ => by omega) hpacket z
  have hrootSource : root i ≤ source :=
    (hupper i).le.trans ((Nat.pow_le_pow_right (by norm_num)
      (show rootBase i + 1 ≤ rootBase i + b / 100 by omega)).trans
      (ndGeom2RootSideCommonFloorShifted_sourceLower hodd hb hfloor hlower z))
  have hlog : Real.log (root i : ℝ) ≤ Real.log (source : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by change (0 : ℝ) < root i; exact_mod_cast Odd.pos (hodd i))
      (by change (0 : ℝ) < source; exact_mod_cast Odd.pos hsourceOdd)
      (by exact_mod_cast hrootSource)
  have hdepth := ndGeom2RootSideCommonFloorShifted_depth_le_logGap
    hodd hb hfloor hlower hupper z
  rcases htarget i with ⟨_, _, m, hmclock, hmone⟩
  refine ⟨Odd.pos hsourceOdd, hsourceOdd, depth + m, ?_, ?_⟩
  · have hpay := mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hlog)
    change (depth + m : ℕ) ≤ C * Real.log (source : ℝ)
    rw [Nat.cast_add]
    change (depth : ℝ) ≤ 250 * (Real.log (source : ℝ) - Real.log (root i : ℝ)) at hdepth
    nlinarith only [hdepth, hmclock, hpay]
  · rw [Nat.add_comm, Function.iterate_add_apply]
    have hit : (Tao.syracuse^[depth]) source = root i :=
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_iterate
        hodd (fun _ => by omega) hpacket z
    rw [hit, hmone]

theorem ndGeom2RootSideCommonFloor_capOne_source_bounds
    {Label : Type*} {root shift : Label → ℕ} {b : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hlower : ∀ i, 16 ^ b ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift 1) :
    let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z;
    let ell := ndGeom2ShiftedWideSymmetricPhysicalLowerScale b (shift i) (root i);
    ell ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ≤ 16 * ell := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let num := 2 ^ shift i * 4 ^ b * root i
  let den := 4 * 2 ^ r * 3 ^ b
  have hden : (0 : ℝ) < (den : ℕ) := by dsimp [den]; positivity
  have h := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
    hodd (fun _ => hb) hlower z
  change (num : ℝ) / den ≤ source ∧ (source : ℝ) ≤ 16 * ((num : ℝ) / den)
  constructor
  · apply (div_le_iff₀ hden).2
    exact_mod_cast (show num ≤ source * den by simpa only [num, den, r, source, i,
      Nat.mul_comm] using h.1)
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).2
    have hu : source * den ≤ 16 * num := by
      have hu' := Nat.mul_le_mul_left 4 h.2
      dsimp only [den, num, r, source, i] at hu' ⊢
      norm_num only [pow_one] at hu'
      nlinarith only [hu']
    exact_mod_cast hu

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def fullTerminalShift
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (i : U.state.Label) : ℕ :=
  Classical.choose (exists_ndGeom2ShiftedWideSymmetricPhysicalLowerScale_mem_twoMul
    hX (hi i).1.le (hi i).2)

theorem fullTerminalShift_spec
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    (i : U.state.Label) :
    U.fullTerminalShift X hX hi i ∈ ndGeom2ShiftedWideSymmetricShiftIndices U.floor ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalLowerScale U.floor
        (U.fullTerminalShift X hX hi i) (U.state.root i) ∧
      ndGeom2ShiftedWideSymmetricPhysicalLowerScale U.floor
        (U.fullTerminalShift X hX hi i) (U.state.root i) < 2 * X :=
  Classical.choose_spec (exists_ndGeom2ShiftedWideSymmetricPhysicalLowerScale_mem_twoMul
    hX (hi i).1.le (hi i).2)

abbrev FullTerminalIncidence
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i)) :=
  NDGeom2PredictableRootSideBoundedOvershootIncidence U.state.Label U.state.root
    (fun _ => U.floor) (U.fullTerminalShift X hX hi) 1

theorem fullTerminal_source_mem_target_and_window
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : U.state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin U.floor (U.state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax U.floor (U.state.root i))
    {C : ℝ} (hC : 250 ≤ C)
    (htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet C)
    (z : U.FullTerminalIncidence X hX hi) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈ oddSyracuseLogTimeOneSet C ∧
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X := by
  have hpacket : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
  have hs := U.fullTerminalShift_spec X hX hi
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  have hb := ndGeom2RootSideCommonFloor_capOne_source_bounds U.state.root_odd
    (by have h := U.floor_twoHundred; omega) hpacket z
  refine ⟨ndGeom2RootSideCommonFloorShifted_source_mem_same_target
    U.state.root_odd U.floor_twoHundred U.floor_le_base U.state.rootLower
    U.state.rootSideRootUpper hC htarget z, hs.2.1.trans hb.1, ?_⟩
  nlinarith only [hb.2, hs.2.2]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
