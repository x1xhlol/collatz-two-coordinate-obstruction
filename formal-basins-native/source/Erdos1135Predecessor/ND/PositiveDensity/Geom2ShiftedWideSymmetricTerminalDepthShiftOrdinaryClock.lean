/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreOrdinaryElevenClock
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalDepthShiftTail

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem balancedTotal_mul_logTwo_lower (j : ℕ) :
    (j : ℝ) * Real.log 3 ≤ (ndBalancedTotal j : ℝ) * Real.log 2 := by
  have hp : (3 : ℝ) ^ j ≤ (2 : ℝ) ^ ndBalancedTotal j := by
    exact_mod_cast three_pow_le_two_pow_ndBalancedTotal j
  simpa only [Real.log_pow] using Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ j) hp

theorem balancedTotal_mul_logTwo_upper (j : ℕ) :
    (ndBalancedTotal j : ℝ) * Real.log 2 ≤ (j : ℝ) * Real.log 3 + Real.log 2 := by
  have hp : (2 : ℝ) ^ ndBalancedTotal j ≤ 2 * (3 : ℝ) ^ j := by
    exact_mod_cast two_pow_ndBalancedTotal_le_two_mul_three_pow j
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ ndBalancedTotal j) hp
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at h
  linarith only [h]

theorem terminalDepthShiftGood_two_mul_depth_le_total_add_eighth
    {b a s : ℕ} {word : List ℕ+} (hlen : word.length = s)
    (hfirst : ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word)
    (hgood : ndTerminalDepthShiftGood b a s) :
    2 * s ≤ Tao.taoTupleWeight word + b / 8 := by
  have hh := hfirst.2.1.2
  unfold ndGeom2ShiftedWideSymmetricHit at hh
  rw [← hlen, List.take_length] at hh
  rw [hlen] at hh
  unfold ndTerminalDepthShiftGood at hgood
  omega

theorem core_band_valuation_mul_logTwo_lower
    {S D W A n : ℕ}
    (hband : 2 * S + ndBalancedTotal D ≤ A + ndBalancedTotal S + 2 * n)
    (hdepth : D ≤ S + W) :
    2 * (D : ℝ) * Real.log 2 - Real.log (4 / 3 : ℝ) * W -
        (2 * (n : ℝ) + 1) * Real.log 2 ≤ (A : ℝ) * Real.log 2 := by
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg : 0 ≤ Real.log (4 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hb : 2 * (S : ℝ) + ndBalancedTotal D ≤ A + ndBalancedTotal S + 2 * (n : ℝ) := by
    exact_mod_cast hband
  have hd : (D : ℝ) ≤ (S : ℝ) + W := by exact_mod_cast hdepth
  have hbL := mul_le_mul_of_nonneg_right hb hL
  have hdg := mul_le_mul_of_nonneg_right hd hg
  have hlog : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  rw [hlog] at hdg ⊢
  nlinarith only [hbL, hdg, balancedTotal_mul_logTwo_lower D, balancedTotal_mul_logTwo_upper S]

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminalPath_valuationWeight_eq_central_add_terminal
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    Tao.taoTupleWeight (Tao.syracuseValuationPNatList
      (U.fullTerminalPath cap n shift K z).depth
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
      (U.fullTerminalPath cap n shift K z).sourceOdd) =
      Tao.taoTupleWeight (U.forwardWord cap n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)) +
        Tao.taoTupleWeight (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z) := by
  rw [(U.fullTerminalPath cap n shift K z).valuation_eq,
    U.fullTerminalPath_word_eq_reverse, Tao.taoTupleWeight_reverse]
  exact Tao.taoTupleWeight_append _ _

theorem fullGoodCoreTerminalPath_valuation_mul_logTwo_lower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K)
    (hc : U.forwardCore cap ndRootCoreWidth n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
    (hg : ndTerminalDepthShiftGood (U.forwardIterate cap n).floor
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z)) :
    let p := U.fullTerminalPath cap n shift K z;
    2 * (p.depth : ℝ) * Real.log 2 -
      Real.log (4 / 3 : ℝ) * U.coreWidthSum cap ndRootCoreWidth n -
      (2 * (n : ℝ) + 1) * Real.log 2 -
      ((U.forwardIterate cap n).floor : ℝ) / 8 * Real.log 2 ≤
        (Tao.taoTupleWeight (Tao.syracuseValuationPNatList p.depth
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) p.sourceOdd) : ℝ) * Real.log 2 := by
  have hcentral := core_band_valuation_mul_logTwo_lower (U.forwardWord_total_band cap n _).1
    (U.forwardCore_depth_band cap ndRootCoreWidth n _ hc).2
  have hterminal := terminalDepthShiftGood_two_mul_depth_le_total_add_eighth
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length z)
    (ndGeom2PredictableRootSideBoundedOvershootIncidence_firstCrossing z) hg
  have ht : 2 * (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z : ℝ) ≤
      (Tao.taoTupleWeight (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z) : ℝ) +
        ((U.forwardIterate cap n).floor : ℝ) / 8 := by
    have hdiv : 8 * ((U.forwardIterate cap n).floor / 8) ≤ (U.forwardIterate cap n).floor :=
      Nat.mul_div_le _ _
    have ht' : 2 * (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z : ℝ) ≤
        (Tao.taoTupleWeight (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z) : ℝ) +
          (((U.forwardIterate cap n).floor / 8 : ℕ) : ℝ) := by exact_mod_cast hterminal
    have hd : 8 * (((U.forwardIterate cap n).floor / 8 : ℕ) : ℝ) ≤
        ((U.forwardIterate cap n).floor : ℝ) := by exact_mod_cast hdiv
    linarith only [ht', hd]
  have htL := mul_le_mul_of_nonneg_right ht (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  dsimp only
  rw [U.fullTerminalPath_valuationWeight_eq_central_add_terminal,
    U.fullTerminalPath_depth_eq_forward_length_add_terminal_depth]
  push_cast
  nlinarith only [hcentral, htL]

theorem fullGoodCoreTerminalPath_depth_add_one_le_log_source_of_width_budget
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hb : 32 ^ 5 ≤ U.floor) (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K)
    (hc : U.forwardCore cap ndRootCoreWidth n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
    (hgood : ndTerminalDepthShiftGood (U.forwardIterate cap n).floor
      (shift (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z))
    {r kappa : ℝ} (hr : 0 ≤ r)
    (hwidth : (U.coreWidthSum cap ndRootCoreWidth n : ℝ) ≤
      r * U.fullClockFloorSum cap n)
    (hcoefficient : r * Real.log (4 / 3 : ℝ) + 219 / 250000 ≤
      (kappa * (2 * Real.log 2 - Real.log (12289 / 4096 : ℝ)) - 1) * (2569 / 9000)) :
    (((U.fullTerminalPath cap n shift K z).depth + 1 : ℕ) : ℝ) ≤
      kappa * Real.log (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) := by
  let p := U.fullTerminalPath cap n shift K z
  let x := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  let M := U.state.root (fullTerminalAncestor z)
  let B : ℝ := U.fullClockFloorSum cap n
  let b : ℝ := (U.forwardIterate cap n).floor
  let b0 : ℝ := U.floor
  let W : ℝ := U.coreWidthSum cap ndRootCoreWidth n
  let L := Real.log 2
  let g := Real.log (4 / 3 : ℝ)
  let h := Real.log (12289 / 4096 : ℝ)
  let gamma := 2 * L - h
  have hL : 0 ≤ L := Real.log_nonneg (by norm_num)
  have hLu : L ≤ (7 / 10 : ℝ) := Real.log_two_lt_d9.le.trans (by norm_num)
  have hg0 : (296 / 1029 : ℝ) ≤ g := by
    have ht := Real.sum_range_le_log_div (x := (1 / 7 : ℝ)) (by norm_num) (by norm_num) 2
    norm_num [Finset.sum_range_succ] at ht
    linarith only [ht]
  have hg : 0 ≤ g := by linarith only [hg0]
  have hlogg : g = 2 * L - Real.log 3 := by
    dsimp [g, L]
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  have hsmall : h ≤ Real.log 3 + 1 / 12288 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12289 / 12288)
    dsimp [h]
    rw [show (12289 / 4096 : ℝ) = 3 * (12289 / 12288) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith only [ht]
  have hgamlo : g - 1 / 12288 ≤ gamma := by dsimp [gamma]; linarith only [hlogg, hsmall]
  have hgam : 0 < gamma := by linarith only [hgamlo, hg0]
  have hgamL : gamma ≤ L := by
    have hh : L ≤ h := Real.log_le_log (by norm_num) (by norm_num)
    dsimp [gamma]
    linarith only [hh]
  have hval := U.fullGoodCoreTerminalPath_valuation_mul_logTwo_lower cap n shift K z hc hgood
  have htime := rawTime_mul_logTwo_le_of_history_floor 4096 (by norm_num) p.depth x p.sourceOdd
    (fun j hj => U.fullTerminalPath_history_floor_4096 cap n shift K z j hj.le)
  rw [p.terminal_eq] at htime
  have htime' : ((p.depth : ℝ) +
      (Tao.taoTupleWeight (Tao.syracuseValuationPNatList p.depth x p.sourceOdd) : ℝ)) * L ≤
      (p.depth : ℝ) * (L + h) + Real.log (x : ℝ) - Real.log (M : ℝ) := by
    convert htime using 1 <;> norm_num [L, h, M]
  change 2 * (p.depth : ℝ) * L - g * W - (2 * (n : ℝ) + 1) * L - b / 8 * L ≤
    (Tao.taoTupleWeight (Tao.syracuseValuationPNatList p.depth x p.sourceOdd) : ℝ) * L at hval
  have hgap : gamma * ((p.depth : ℝ) + 1) ≤
      Real.log (x : ℝ) - Real.log (M : ℝ) + g * W + (2 * (n : ℝ) + 1) * L + b / 8 * L + gamma := by
    dsimp only [gamma]
    nlinarith only [htime', hval]
  have hseed : 4 * b0 * L ≤ Real.log (M : ℝ) := by
    have hr : (16 : ℝ) ^ U.floor ≤ M := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num)
        (U.floor_le_base (fullTerminalAncestor z))).trans (U.state.rootLower (fullTerminalAncestor z))
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < 16 ^ U.floor) hr
    rw [Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at ht
    norm_num only [Nat.cast_ofNat] at ht
    dsimp [b0, L]
    nlinarith only [ht]
  have hb0 : (1 : ℝ) ≤ b0 := by
    dsimp only [b0]
    exact_mod_cast (by have := U.floor_twoHundred; omega : 1 ≤ U.floor)
  have hseedPay : b0 / 8 * L + gamma ≤ Real.log (M : ℝ) := by
    have hbL := mul_le_mul_of_nonneg_right hb0 hL
    nlinarith only [hseed, hgamL, hbL, hL]
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hw : W ≤ r * B := hwidth
  have hwg := mul_le_mul_of_nonneg_right hw hg
  have hbLast : 100 * b ≤ 100 * b0 + B := by
    dsimp only [b, b0, B]
    exact_mod_cast U.hundred_mul_forwardFloor_le_initial_add_fullClockFloorSum cap n
  have hbLastL := mul_le_mul_of_nonneg_right hbLast hL
  have hcount : (32 : ℝ) ^ 5 * ((n : ℝ) + 1) ≤ B := by
    dsimp only [B]
    exact_mod_cast (Nat.mul_le_mul_right (n + 1) hb).trans
      (by simpa only [Nat.mul_comm] using U.fullClockFloorSum_ge_count_mul_floor cap n)
  have hround : (2 * (n : ℝ) + 1) * L ≤ B / 1000000 := by
    have ht := mul_le_mul_of_nonneg_left hLu (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
    norm_num only [show (32 : ℝ) ^ 5 = 33554432 by norm_num] at hcount
    nlinarith only [hcount, ht, hL, Nat.cast_nonneg (α := ℝ) n]
  have hLuB := mul_le_mul_of_nonneg_right hLu hB
  have hbudget : gamma * ((p.depth : ℝ) + 1) ≤
      Real.log (x : ℝ) + (r * g + 219 / 250000) * B := by
    nlinarith only [hgap, hseedPay, hwg, hbLastL, hround, hLuB]
  have hcoef : r * g + 219 / 250000 ≤ (kappa * gamma - 1) * (2569 / 9000) := hcoefficient
  have hcoef0 : 0 ≤ kappa * gamma - 1 := by
    have hrg := mul_nonneg hr hg
    linarith only [hcoef, hrg]
  have hcoefB := mul_le_mul_of_nonneg_right hcoef hB
  have hlog := U.fullTerminalPath_log_source_ge_floorSum hb cap n shift K z
  have hlog' : (2569 / 9000 : ℝ) * B ≤ Real.log (x : ℝ) := by
    convert hlog using 1 <;> norm_num [B, x]
  have hlogC := mul_le_mul_of_nonneg_left hlog' hcoef0
  have hfinal : gamma * ((p.depth : ℝ) + 1) ≤ gamma * (kappa * Real.log (x : ℝ)) := by
    nlinarith only [hbudget, hcoefB, hlogC]
  change ((p.depth + 1 : ℕ) : ℝ) ≤ _
  push_cast
  nlinarith only [hgam, hfinal]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
