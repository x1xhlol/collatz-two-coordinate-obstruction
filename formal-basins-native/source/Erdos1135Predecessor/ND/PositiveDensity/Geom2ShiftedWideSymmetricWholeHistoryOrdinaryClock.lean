/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideGeometricFullTerminalCount
import Erdos1135Predecessor.ND.PositiveDensity.SyracuseWholeHistoryOrdinaryClock

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem rootSidePhysicalBlock_history_floor_4096
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : ∀ i, 9 ≤ base i)
    (hlower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K) :
    ∀ j ≤ ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z,
      4096 ≤ (Tao.syracuse^[j]) (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
  let b := base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  let d := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  have hd' := ndGeom2ShiftedWideSymmetricSelectedDepth_le_two_mul_add_one
      (ndGeom2PredictableRootSideBoundedOvershootIncidence_depth_mem z)
  have hd : d ≤ 2 * (b + 1) := by dsimp [d, b]; omega
  have hb9 : 9 ≤ b := hb _
  have hpow : 4096 * 2 ^ d ≤ 16 ^ b := by
    calc
      _ = 2 ^ (12 + d) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ (4 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  apply history_floor_of_terminal_bound 4096 d _
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd hodd hb hlower z)
  rw [ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_iterate hodd hb hlower z]
  exact hpow.trans (hlower _)

theorem NDGeom2RootSideSyracusePath.history_floor_appendRootSideIncidence
    {Label : Type*} {root base shift : Label → ℕ} {K source : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : ∀ i, 9 ≤ base i)
    (hlower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K)
    (p : NDGeom2RootSideSyracusePath source
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z))
    (hp : ∀ j ≤ p.depth, 4096 ≤ (Tao.syracuse^[j]) source) :
    ∀ j ≤ (p.appendRootSideIncidence hodd hb hlower z).depth,
      4096 ≤ (Tao.syracuse^[j]) source := by
  intro j hj
  change j ≤ p.depth + ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z at hj
  by_cases hsmall : j ≤ p.depth
  · exact hp j hsmall
  · have h := rootSidePhysicalBlock_history_floor_4096 hodd hb hlower z
      (j - p.depth) (by omega)
    have heq := congrArg (fun a : ℕ => (Tao.syracuse^[j - p.depth]) a) p.terminal_eq
    dsimp only at heq
    rw [← Function.iterate_add_apply,
      Nat.sub_add_cancel (by omega : p.depth ≤ j)] at heq
    exact h.trans_eq heq.symm

theorem rootSidePhysicalBlock_log_source_growth
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hodd : ∀ i, Odd (root i)) (hb : ∀ i, 9 ≤ base i)
    (hlower : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K) :
    let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z;
    Real.log (root i : ℝ) + (base i : ℝ) * Real.log (4 / 3 : ℝ) +
        ((shift i : ℝ) - ndGeom2ShiftedWideSymmetricShiftRadius (base i)) * Real.log 2 -
          Real.log 4 ≤
      Real.log (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) := by
  intro i
  let b := base i
  let a := shift i
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let x := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hM : (0 : ℝ) < root i := by exact_mod_cast Odd.pos (hodd i)
  have hx : (0 : ℝ) < x := by
    exact_mod_cast Odd.pos
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd hodd hb hlower z)
  have hs : (2 : ℝ) ^ a * 4 ^ b * root i ≤ 4 * 2 ^ r * 3 ^ b * x := by
    exact_mod_cast (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
      hodd hb hlower z).1
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ a * 4 ^ b * root i) hs
  have hleft : Real.log ((2 : ℝ) ^ a * 4 ^ b * root i) =
      a * Real.log 2 + b * Real.log 4 + Real.log (root i : ℝ) := by
    rw [Real.log_mul (by positivity) hM.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  have hright : Real.log (4 * (2 : ℝ) ^ r * 3 ^ b * x) =
      Real.log 4 + r * Real.log 2 + b * Real.log 3 + Real.log (x : ℝ) := by
    rw [Real.log_mul (by positivity) hx.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
  rw [hleft, hright] at hlog
  rw [Real.log_div (by norm_num) (by norm_num)]
  change Real.log (root i : ℝ) + (b : ℝ) * (Real.log 4 - Real.log 3) +
    ((a : ℝ) - r) * Real.log 2 - Real.log 4 ≤ Real.log (x : ℝ)
  nlinarith only [hlog]

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

def fullClockFloorSum (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : ℕ → ℕ
  | 0 => U.floor
  | n + 1 => U.floor + (U.next (cap 0)).fullClockFloorSum (ndGeom2RootSideCapTail cap) n

theorem fullClockFloorSum_ge_count_mul_floor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    (n + 1) * U.floor ≤ U.fullClockFloorSum cap n := by
  induction n generalizing U cap with
  | zero => simp [fullClockFloorSum]
  | succ n ih =>
      have h := ih (U.next (cap 0)) (ndGeom2RootSideCapTail cap)
      have hfloor : U.floor ≤ (U.next (cap 0)).floor := by
        change U.floor ≤ U.floor + U.floor / 100; omega
      have hm := Nat.mul_le_mul_left (n + 1) hfloor
      simp only [fullClockFloorSum]
      nlinarith only [h, hm]

theorem hundred_mul_forwardFloor_le_initial_add_fullClockFloorSum
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    100 * (U.forwardIterate cap n).floor ≤
      100 * U.floor + U.fullClockFloorSum cap n := by
  induction n generalizing U cap with
  | zero => simp [forwardIterate, fullClockFloorSum]
  | succ n ih =>
      have h := ih (U.next (cap 0)) (ndGeom2RootSideCapTail cap)
      have hd := Nat.div_mul_le_self U.floor 100
      change 100 * _ ≤ 100 * (U.floor + U.floor / 100) + _ at h
      simp only [forwardIterate, fullClockFloorSum]
      omega

theorem fullTerminalPath_log_source_growth
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    Real.log (U.state.root (fullTerminalAncestor z) : ℝ) +
        (U.fullClockFloorSum cap n : ℝ) * Real.log (4 / 3 : ℝ) -
        (ndGeom2ShiftedWideSymmetricShiftRadius (U.forwardIterate cap n).floor : ℝ) *
          Real.log 2 - ((n + 1 : ℕ) : ℝ) * Real.log 4 ≤
      Real.log (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) := by
  induction n generalizing U cap with
  | zero =>
      have hroot : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
        (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
      have h := rootSidePhysicalBlock_log_source_growth U.state.root_odd
        (fun _ => by have hf := U.floor_twoHundred; omega) hroot z
      dsimp only at h
      have ha : 0 ≤ (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) : ℝ) *
          Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
      convert (sub_le_self _ ha).trans h using 1
      simp only [fullClockFloorSum, forwardIterate, Nat.zero_add, Nat.cast_one,
        one_mul, fullTerminalAncestor, forwardAncestor]
      ring
  | succ n ih =>
      have ht := ih (U.next (cap 0)) (ndGeom2RootSideCapTail cap) shift z
      let first := U.forwardFirstIncidence cap n
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
      have hroot : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
        (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
      have he := rootSidePhysicalBlock_log_source_growth U.state.root_odd
        (fun _ => by have hf := U.floor_twoHundred; omega) hroot
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical first)
      change Real.log (U.state.root (fullTerminalAncestor z) : ℝ) +
        (U.floor : ℝ) * Real.log (4 / 3 : ℝ) +
        ((ndGeom2ShiftedWideSymmetricShiftRadius U.floor : ℝ) -
          ndGeom2ShiftedWideSymmetricShiftRadius U.floor) * Real.log 2 - Real.log 4 ≤
        Real.log ((U.next (cap 0)).state.root (fullTerminalAncestor z) : ℝ) at he
      simp only [sub_self, zero_mul, add_zero] at he
      simp only [fullClockFloorSum, forwardIterate, Nat.cast_add, Nat.cast_one] at ht ⊢
      linarith only [ht, he]

theorem fullTerminalPath_log_source_ge_floorSum
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hb : 32 ^ 5 ≤ U.floor) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    (64 / 225 + 1 / 1000 : ℝ) * U.fullClockFloorSum cap n ≤
      Real.log (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) := by
  let B := U.fullClockFloorSum cap n
  let b := U.floor
  let last := (U.forwardIterate cap n).floor
  let r := ndGeom2ShiftedWideSymmetricShiftRadius last
  let M := U.state.root (fullTerminalAncestor z)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl2u : Real.log 2 ≤ (7 / 10 : ℝ) := Real.log_two_lt_d9.le.trans (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hl43 : (296 / 1029 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
    have h := Real.sum_range_le_log_div (x := (1 / 7 : ℝ)) (by norm_num) (by norm_num) 2
    norm_num [Finset.sum_range_succ] at h
    linarith only [h]
  have hseed : 4 * (b : ℝ) * Real.log 2 ≤ Real.log (M : ℝ) := by
    have hroot : (16 : ℝ) ^ b ≤ M := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base
        (fullTerminalAncestor z))).trans (U.state.rootLower (fullTerminalAncestor z))
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 16 ^ b) hroot
    rw [Real.log_pow, hl16] at h
    nlinarith only [h]
  have hrad : (10 : ℝ) * r ≤ 3 * (last : ℝ) + 5 := by
    exact_mod_cast ten_mul_ndGeom2ShiftedWideSymmetricShiftRadius_le_three_mul_add_five
      (U.forwardIterate cap n).floor_twoHundred
  have hlast : (100 : ℝ) * last ≤ 100 * (b : ℝ) + B := by
    exact_mod_cast U.hundred_mul_forwardFloor_le_initial_add_fullClockFloorSum cap n
  have hr : (r : ℝ) ≤ (3 / 10 : ℝ) * b + (3 / 1000 : ℝ) * B + 1 / 2 := by
    linarith only [hrad, hlast]
  have hrlog := mul_le_mul_of_nonneg_right hr hl2
  have hb200 : (200 : ℝ) ≤ b := by exact_mod_cast U.floor_twoHundred
  have hseedSlack : 0 ≤ ((37 / 10 : ℝ) * b - 1 / 2) * Real.log 2 :=
    mul_nonneg (by linarith only [hb200]) hl2
  have hg := U.fullTerminalPath_log_source_growth cap n shift K z
  have hbase : (32 ^ 5 : ℕ) * (n + 1) ≤ B :=
    (Nat.mul_le_mul_right (n + 1) hb).trans (by
      simpa only [Nat.mul_comm] using U.fullClockFloorSum_ge_count_mul_floor cap n)
  have hcount : ((n + 1 : ℕ) : ℝ) ≤ (B : ℝ) / 32 ^ 5 := by
    have h : (32 ^ 5 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast hbase
    linarith only [h]
  have hcountLog := mul_le_mul_of_nonneg_right hcount hl2
  have hupperLog := mul_le_mul_of_nonneg_left hl2u (show (0 : ℝ) ≤ B by positivity)
  have hlowerLog := mul_le_mul_of_nonneg_left hl43 (show (0 : ℝ) ≤ B by positivity)
  rw [hl4] at hg
  change Real.log (M : ℝ) + (B : ℝ) * Real.log (4 / 3 : ℝ) -
    (r : ℝ) * Real.log 2 - ((n + 1 : ℕ) : ℝ) * (2 * Real.log 2) ≤ _ at hg
  nlinarith only [hg, hseed, hrlog, hseedSlack, hcountLog, hupperLog, hlowerLog,
    show (0 : ℝ) ≤ B by positivity]

theorem fullTerminalPath_history_floor_4096
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    ∀ j ≤ (U.fullTerminalPath cap n shift K z).depth,
      4096 ≤ (Tao.syracuse^[j]) (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
  induction n generalizing U cap with
  | zero =>
      have hroot : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
        (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
      have hb : ∀ _ : U.state.Label, 9 ≤ U.floor := fun _ => by
        have h := U.floor_twoHundred; omega
      simpa only [fullTerminalPath, NDGeom2RootSideSyracusePath.appendRootSideIncidence_depth,
        NDGeom2RootSideSyracusePath.nil, Nat.zero_add] using
        rootSidePhysicalBlock_history_floor_4096 U.state.root_odd hb hroot z
  | succ n ih =>
      have hroot : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
        (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
      have hb : ∀ _ : U.state.Label, 9 ≤ U.floor := fun _ => by
        have h := U.floor_twoHundred; omega
      let first := U.forwardFirstIncidence cap n
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
      let p := (U.next (cap 0)).fullTerminalPath (ndGeom2RootSideCapTail cap) n shift K z
      exact p.history_floor_appendRootSideIncidence U.state.root_odd hb hroot
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical first)
        (ih (U.next (cap 0)) (ndGeom2RootSideCapTail cap) shift z)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
