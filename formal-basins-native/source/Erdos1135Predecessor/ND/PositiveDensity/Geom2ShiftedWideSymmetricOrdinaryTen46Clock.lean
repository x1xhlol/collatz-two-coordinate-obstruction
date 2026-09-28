/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftOrdinaryClock

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem rootCoreWidth_mul_le_of_fifth_power {b H q : ℕ}
    (hH : 1 ≤ H) (hb : H ^ 5 ≤ b) (hq : 2 * q ≤ H ^ 2) :
    q * ndRootCoreWidth b ≤ b := by
  have hb1 : 1 ≤ b := (one_le_pow₀ hH).trans hb
  have hbH : (H : ℝ) ^ 5 ≤ b := by exact_mod_cast hb
  have h2 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (H : ℝ) ^ 5)
    hbH (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg H)] at h2
  norm_num at h2
  have hprod : (b : ℝ) ^ (3 / 5 : ℝ) * (b : ℝ) ^ (2 / 5 : ℝ) = b := by
    rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < b))]
    norm_num
  have hp := Real.rpow_nonneg (Nat.cast_nonneg b) (3 / 5 : ℝ)
  have hw := rootCoreWidth_upper hb1
  have hqR : (2 : ℝ) * q ≤ (H : ℝ) ^ 2 := by exact_mod_cast hq
  have hm := mul_le_mul_of_nonneg_left (hqR.trans h2) hp
  have hwq := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (α := ℝ) q)
  exact_mod_cast (show (q : ℝ) * ndRootCoreWidth b ≤ b by
    nlinarith only [hm, hwq, hprod])

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem coreWidthSum_mul_le_of_fifth_power
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    {H q : ℕ} (hH : 1 ≤ H) (hb : H ^ 5 ≤ U.floor) (hq : 2 * q ≤ H ^ 2)
    (cap : ℕ → ℕ) (n : ℕ) :
    q * U.coreWidthSum cap ndRootCoreWidth n ≤ U.coreBaseSum cap n := by
  induction n generalizing U cap with
  | zero => simp [coreWidthSum, coreBaseSum]
  | succ n ih =>
      have hb' : H ^ 5 ≤ (U.next (cap 0)).floor := by
        change H ^ 5 ≤ U.floor + U.floor / 100; omega
      have ht := ih (U.next (cap 0)) hb' (ndGeom2RootSideCapTail cap)
      have hf := rootCoreWidth_mul_le_of_fifth_power hH hb hq
      simpa only [coreWidthSum, coreBaseSum, Nat.mul_add] using Nat.add_le_add hf ht

theorem fullGoodCoreTerminalPath_depth_add_one_le_ten46_budget
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hb : 512 ^ 5 ≤ U.floor) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K)
    (hc : U.forwardCore cap ndRootCoreWidth n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
    (hg : ndTerminalDepthShiftGood (U.forwardIterate cap n).floor
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)) :
    (((U.fullTerminalPath cap n shift K z).depth + 1 : ℕ) : ℝ) ≤
      (34881 / 10000 : ℝ) * Real.log (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) := by
  have hb32 : 32 ^ 5 ≤ U.floor := (by norm_num : (32 : ℕ) ^ 5 ≤ 512 ^ 5).trans hb
  apply U.fullGoodCoreTerminalPath_depth_add_one_le_log_source_of_width_budget
    hb32 cap n shift K z hc hg (r := 1 / 100000) (by norm_num)
  · have hw := U.coreWidthSum_mul_le_of_fifth_power (by norm_num : 1 ≤ 512) hb
      (by norm_num : 2 * 100000 ≤ 512 ^ 2) cap n
    have hs := U.fullClockFloorSum_eq_coreBaseSum_add_terminalFloor cap n
    have ht : 100000 * U.coreWidthSum cap ndRootCoreWidth n ≤ U.fullClockFloorSum cap n := by omega
    have htR : (100000 : ℝ) * U.coreWidthSum cap ndRootCoreWidth n ≤ U.fullClockFloorSum cap n := by
      exact_mod_cast ht
    linarith only [htR]
  · have hg0 : (296 / 1029 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
      have ht := Real.sum_range_le_log_div (x := (1 / 7 : ℝ)) (by norm_num) (by norm_num) 2
      norm_num [Finset.sum_range_succ] at ht
      linarith only [ht]
    have hlogg : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.log_pow]
      norm_num
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12289 / 12288)
    have hs : Real.log (12289 / 4096 : ℝ) ≤ Real.log 3 + 1 / 12288 := by
      rw [show (12289 / 4096 : ℝ) = 3 * (12289 / 12288) by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      linarith only [ht]
    nlinarith only [hg0, hlogg, hs]

theorem terminalDepthShift_ten46_coefficient :
    (34881 / 10000 : ℝ) * (Real.log 2 + Real.log (12289 / 4096 : ℝ)) + 1 ≤
      (523 / 50 : ℝ) * Real.log 2 := by
  have hp : (3 : ℝ) ^ 200 < (2 : ℝ) ^ 317 := by
    rw [show (317 : ℕ) = 200 + 117 by rfl, pow_add]
    norm_num
  have h3 := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ 200) hp
  rw [Real.log_pow, Real.log_pow] at h3
  norm_num only [Nat.cast_ofNat] at h3
  have hsmall := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12289 / 12288)
  have hinc : Real.log (12289 / 4096 : ℝ) ≤ Real.log 3 + 1 / 12288 := by
    rw [show (12289 / 4096 : ℝ) = 3 * (12289 / 12288) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith only [hsmall]
  nlinarith only [h3, hinc, Real.log_two_gt_d9]

theorem fullGoodCoreTerminal_source_mem_rawCollatzLogTimeOneSet_ten46
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hb : 512 ^ 5 ≤ U.floor)
    (hseed : ∀ i, Tao.syracuse (U.state.root i) = 1)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K)
    (hc : U.forwardCore cap ndRootCoreWidth n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
    (hg : ndTerminalDepthShiftGood (U.forwardIterate cap n).floor
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈
      rawCollatzLogTimeOneSet (523 / 50 : ℝ) := by
  let x := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let p := U.fullTerminalPath cap n shift K z
  let d := p.depth + 1
  have hhit : (Tao.syracuse^[d]) x = 1 := by
    change (Tao.syracuse^[p.depth + 1]) x = 1
    rw [Function.iterate_succ_apply', p.terminal_eq, hseed]
  have htime := rawTime_mul_logTwo_le_of_history_floor 4096 (by norm_num) d x p.sourceOdd
    (fun j hj => U.fullTerminalPath_history_floor_4096 cap n shift K z j (by
      dsimp [d, p] at hj; omega))
  rw [hhit, Nat.cast_one, Real.log_one, sub_zero] at htime
  have htime' : ((d + Tao.taoTupleWeight (Tao.syracuseValuationPNatList d x p.sourceOdd) : ℕ) : ℝ) *
      Real.log 2 ≤ (d : ℝ) * (Real.log 2 + Real.log (12289 / 4096 : ℝ)) + Real.log (x : ℝ) := by
    convert htime using 1
    norm_num
  have hd := U.fullGoodCoreTerminalPath_depth_add_one_le_ten46_budget hb cap n shift K z hc hg
  have hA : 0 ≤ Real.log 2 + Real.log (12289 / 4096 : ℝ) :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
  have hdm := mul_le_mul_of_nonneg_right hd hA
  have hxlog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast Odd.pos p.sourceOdd)
  have hcm := mul_le_mul_of_nonneg_right terminalDepthShift_ten46_coefficient hxlog
  refine ⟨Odd.pos p.sourceOdd,
    d + Tao.taoTupleWeight (Tao.syracuseValuationPNatList d x p.sourceOdd), ?_, ?_⟩
  · apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    nlinarith only [htime', hdm, hcm]
  · rw [Tao.collatz_iterate_syracuseValuationTime]
    exact hhit

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
