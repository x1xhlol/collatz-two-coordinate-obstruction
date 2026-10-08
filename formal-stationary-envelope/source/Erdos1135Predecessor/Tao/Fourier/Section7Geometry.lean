/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection7_log9_div_log2_lt_sixteen_fifths :
    Real.log 9 / Real.log 2 < (16 / 5 : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (9 : ℝ) ^ 5 < (2 : ℝ) ^ 16 := by norm_num
  have hlogpow : Real.log ((9 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 16) :=
    Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hdiv : Real.log (9 : ℝ) < (16 / 5 : ℝ) * Real.log (2 : ℝ) := by
    calc
      Real.log (9 : ℝ) = (5 * Real.log (9 : ℝ)) / 5 := by ring
      _ < (16 * Real.log (2 : ℝ)) / 5 :=
        div_lt_div_of_pos_right hlogpow (by norm_num)
      _ = (16 / 5 : ℝ) * Real.log (2 : ℝ) := by ring
  exact (div_lt_iff₀ hlog2).2 hdiv

structure TaoSection7Point where
  j : ℕ+
  l : ℤ
deriving DecidableEq

namespace TaoSection7Point

def jReal (p : TaoSection7Point) : ℝ :=
  (p.j : ℕ)

def lReal (p : TaoSection7Point) : ℝ :=
  p.l

def distSq (p q : TaoSection7Point) : ℝ :=
  (p.jReal - q.jReal) ^ 2 + (p.lReal - q.lReal) ^ 2

theorem distSq_comm (p q : TaoSection7Point) :
    p.distSq q = q.distSq p := by
  dsimp [distSq]
  ring

def right (p : TaoSection7Point) : TaoSection7Point :=
  ⟨⟨(p.j : ℕ) + 1, by omega⟩, p.l⟩

def down (p : TaoSection7Point) : TaoSection7Point :=
  ⟨p.j, p.l - 1⟩

def left (p : TaoSection7Point) (h : 1 < (p.j : ℕ)) : TaoSection7Point :=
  ⟨⟨(p.j : ℕ) - 1, by omega⟩, p.l⟩

@[simp] theorem right_j (p : TaoSection7Point) :
    ((p.right.j : ℕ) : ℕ) = (p.j : ℕ) + 1 :=
  rfl

@[simp] theorem right_l (p : TaoSection7Point) :
    p.right.l = p.l :=
  rfl

@[simp] theorem down_j (p : TaoSection7Point) :
    p.down.j = p.j :=
  rfl

@[simp] theorem down_l (p : TaoSection7Point) :
    p.down.l = p.l - 1 :=
  rfl

end TaoSection7Point

noncomputable section

structure TaoSection7Triangle where
  cornerJ : ℕ+
  cornerL : ℤ
  size : ℝ

namespace TaoSection7Triangle

def topLeft (Δ : TaoSection7Triangle) : TaoSection7Point :=
  ⟨Δ.cornerJ, Δ.cornerL⟩

def horizontalDepth (Δ : TaoSection7Triangle) (p : TaoSection7Point) : ℕ :=
  (p.j : ℕ) - (Δ.cornerJ : ℕ)

def verticalDepth (Δ : TaoSection7Triangle) (p : TaoSection7Point) : ℤ :=
  Δ.cornerL - p.l

def Mem (Δ : TaoSection7Triangle) (p : TaoSection7Point) : Prop :=
  Δ.cornerJ ≤ p.j ∧
    p.l ≤ Δ.cornerL ∧
      ((Δ.horizontalDepth p : ℕ) : ℝ) * Real.log 9 +
          ((Δ.verticalDepth p : ℤ) : ℝ) * Real.log 2 ≤ Δ.size

theorem mem_time_ge {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hp : Δ.Mem p) :
    Δ.cornerJ ≤ p.j :=
  hp.1

theorem mem_height_le {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hp : Δ.Mem p) :
    p.l ≤ Δ.cornerL :=
  hp.2.1

theorem mem_weight_le_size {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hp : Δ.Mem p) :
    ((Δ.horizontalDepth p : ℕ) : ℝ) * Real.log 9 +
        ((Δ.verticalDepth p : ℤ) : ℝ) * Real.log 2 ≤ Δ.size :=
  hp.2.2

theorem mem_topLeft_iff (Δ : TaoSection7Triangle) :
    Δ.Mem Δ.topLeft ↔ 0 ≤ Δ.size := by
  simp [Mem, horizontalDepth, verticalDepth, topLeft]

theorem topLeft_mem_of_nonneg {Δ : TaoSection7Triangle} (hsize : 0 ≤ Δ.size) :
    Δ.Mem Δ.topLeft :=
  (mem_topLeft_iff Δ).2 hsize

theorem verticalDepth_nonneg_of_mem {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hp : Δ.Mem p) :
    0 ≤ Δ.verticalDepth p := by
  dsimp [verticalDepth]
  exact sub_nonneg.mpr hp.2.1

noncomputable def lowerTip (Δ : TaoSection7Triangle) : ℝ :=
  (Δ.cornerL : ℝ) - Δ.size / Real.log 2

theorem lowerTip_le_lReal_of_mem
    {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hp : Δ.Mem p) :
    Δ.lowerTip ≤ p.lReal := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9_nonneg : 0 ≤ Real.log 9 := (Real.log_pos (by norm_num : (1 : ℝ) < 9)).le
  have hweight := mem_weight_le_size hp
  have hhor_nonneg :
      0 ≤ ((Δ.horizontalDepth p : ℕ) : ℝ) * Real.log 9 :=
    mul_nonneg (Nat.cast_nonneg _) hlog9_nonneg
  have hvert :
      ((Δ.verticalDepth p : ℤ) : ℝ) * Real.log 2 ≤ Δ.size := by
    linarith
  have hbase :
      ((Δ.verticalDepth p : ℤ) : ℝ) ≤ Δ.size / Real.log 2 :=
    (le_div_iff₀' hlog2).2 (by simpa [mul_comm] using hvert)
  dsimp [lowerTip, verticalDepth, TaoSection7Point.lReal] at hbase ⊢
  rw [Int.cast_sub] at hbase
  linarith

noncomputable def rowRightEnd (Δ : TaoSection7Triangle) (lStar : ℤ) : ℝ :=
  ((Δ.cornerJ : ℕ) : ℝ) +
    (Δ.size - ((Δ.cornerL - lStar : ℤ) : ℝ) * Real.log 2) / Real.log 9

theorem rowRightEnd_eq_cornerJ_add_lStar_sub_lowerTip
    (Δ : TaoSection7Triangle) (lStar : ℤ) :
    Δ.rowRightEnd lStar =
      ((Δ.cornerJ : ℕ) : ℝ) +
        (((lStar : ℤ) : ℝ) - Δ.lowerTip) * Real.log 2 / Real.log 9 := by
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlog9 : Real.log 9 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  dsimp [rowRightEnd, lowerTip]
  field_simp [hlog2, hlog9]
  rw [Int.cast_sub]
  ring_nf

def rowJInterval (Δ : TaoSection7Triangle) (lStar : ℤ) : Set ℕ+ :=
  {jStar | Δ.cornerJ ≤ jStar ∧ ((jStar : ℕ) : ℝ) ≤ Δ.rowRightEnd lStar}

theorem horizontalDepth_real_eq_sub_of_cornerJ_le
    {Δ : TaoSection7Triangle} {jStar : ℕ+} {lStar : ℤ}
    (hj : Δ.cornerJ ≤ jStar) :
    ((Δ.horizontalDepth ⟨jStar, lStar⟩ : ℕ) : ℝ) =
      ((jStar : ℕ) : ℝ) - ((Δ.cornerJ : ℕ) : ℝ) := by
  have hjNat : (Δ.cornerJ : ℕ) ≤ (jStar : ℕ) := by
    exact_mod_cast hj
  simp [horizontalDepth, Nat.cast_sub hjNat]

theorem verticalDepth_le_log9_div_log2_mul_rightGap_of_mem_rightEdge
    {old : TaoSection7Triangle} {p : TaoSection7Point} {S M cutoff : ℝ}
    (hp : old.Mem p)
    (hS : S = ((old.verticalDepth p : ℤ) : ℝ))
    (hright : ((old.cornerJ : ℕ) : ℝ) + old.size / Real.log 9 ≤ cutoff)
    (hM : M = cutoff - p.jReal) :
    S ≤ (Real.log 9 / Real.log 2) * M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num : (1 : ℝ) < 9)
  have hdepth :=
    horizontalDepth_real_eq_sub_of_cornerJ_le
      (Δ := old) (jStar := p.j) (lStar := p.l) hp.1
  have hweight := mem_weight_le_size hp
  have hweightS :
      (p.jReal - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 + S * Real.log 2 ≤
        old.size := by
    simpa [TaoSection7Point.jReal, hdepth, hS] using hweight
  have hsize_div : old.size / Real.log 9 ≤ cutoff - ((old.cornerJ : ℕ) : ℝ) := by
    linarith
  have hsize_le : old.size ≤ (cutoff - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 := by
    rw [div_le_iff₀ hlog9] at hsize_div
    nlinarith
  have hSlog_le : S * Real.log 2 ≤ (cutoff - p.jReal) * Real.log 9 := by
    have hsub :
        (cutoff - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 -
            (p.jReal - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 =
          (cutoff - p.jReal) * Real.log 9 := by
      ring
    linarith
  rw [hM]
  have htarget :
      (Real.log 9 / Real.log 2) * (cutoff - p.jReal) =
        ((cutoff - p.jReal) * Real.log 9) / Real.log 2 := by
    ring
  rw [htarget]
  rw [le_div_iff₀ hlog2]
  exact hSlog_le

theorem mem_of_mem_rowJInterval
    {Δ : TaoSection7Triangle} {jStar : ℕ+} {lStar : ℤ}
    (hj : jStar ∈ Δ.rowJInterval lStar)
    (hl : lStar ≤ Δ.cornerL) :
    Δ.Mem ⟨jStar, lStar⟩ := by
  rcases hj with ⟨hjleft, hjright⟩
  refine ⟨hjleft, hl, ?_⟩
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hdepth :=
    horizontalDepth_real_eq_sub_of_cornerJ_le
      (Δ := Δ) (jStar := jStar) (lStar := lStar) hjleft
  have hsub :
      ((jStar : ℕ) : ℝ) - ((Δ.cornerJ : ℕ) : ℝ) ≤
        (Δ.size - ((Δ.cornerL - lStar : ℤ) : ℝ) * Real.log 2) / Real.log 9 := by
    dsimp [rowJInterval, rowRightEnd] at hjright
    linarith
  have hmul_left :
      Real.log 9 * (((jStar : ℕ) : ℝ) - ((Δ.cornerJ : ℕ) : ℝ)) ≤
        Δ.size - ((Δ.cornerL - lStar : ℤ) : ℝ) * Real.log 2 :=
    (le_div_iff₀' hlog9).mp hsub
  have hmul :
      (((jStar : ℕ) : ℝ) - ((Δ.cornerJ : ℕ) : ℝ)) * Real.log 9 ≤
        Δ.size - ((Δ.cornerL - lStar : ℤ) : ℝ) * Real.log 2 :=
    by simpa [mul_comm] using hmul_left
  dsimp [verticalDepth]
  rw [hdepth]
  linarith

theorem mem_of_row_bounds
    {Δ : TaoSection7Triangle} {jStar : ℕ+} {lStar : ℤ}
    (hjLeft : Δ.cornerJ ≤ jStar)
    (hjRight : ((jStar : ℕ) : ℝ) ≤ Δ.rowRightEnd lStar)
    (hl : lStar ≤ Δ.cornerL) :
    Δ.Mem ⟨jStar, lStar⟩ :=
  mem_of_mem_rowJInterval ⟨hjLeft, hjRight⟩ hl

theorem cornerJ_le_rowRightEnd_of_lowerTip_le
    {Δ : TaoSection7Triangle} {lStar : ℤ}
    (hlow : Δ.lowerTip ≤ (lStar : ℝ)) :
    ((Δ.cornerJ : ℕ) : ℝ) ≤ Δ.rowRightEnd lStar := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hsize :
      (((Δ.cornerL - lStar : ℤ) : ℝ) * Real.log 2) ≤ Δ.size := by
    have hraw :
        ((Δ.cornerL : ℝ) - (lStar : ℝ)) * Real.log 2 ≤ Δ.size := by
      dsimp [lowerTip] at hlow
      have hle_div :
          (Δ.cornerL : ℝ) - (lStar : ℝ) ≤ Δ.size / Real.log 2 := by
        linarith
      simpa [mul_comm] using (le_div_iff₀' hlog2).1 hle_div
    simpa [Int.cast_sub] using hraw
  have hnonneg :
      0 ≤ (Δ.size - (((Δ.cornerL - lStar : ℤ) : ℝ) * Real.log 2)) /
          Real.log 9 :=
    div_nonneg (sub_nonneg.mpr hsize) hlog9.le
  dsimp [rowRightEnd]
  linarith

theorem jReal_le_rowRightEnd_of_mem
    {Δ : TaoSection7Triangle} {p : TaoSection7Point}
    (hp : Δ.Mem p) :
    p.jReal ≤ Δ.rowRightEnd p.l := by
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hcorner := mem_time_ge hp
  have hdepth :=
    horizontalDepth_real_eq_sub_of_cornerJ_le
      (Δ := Δ) (jStar := p.j) (lStar := p.l) hcorner
  have hweight := mem_weight_le_size hp
  have hmul :
      (p.jReal - ((Δ.cornerJ : ℕ) : ℝ)) * Real.log 9 ≤
        Δ.size - (((Δ.cornerL - p.l : ℤ) : ℝ) * Real.log 2) := by
    rw [hdepth] at hweight
    have hweight' :
        (p.jReal - ((Δ.cornerJ : ℕ) : ℝ)) * Real.log 9 +
            (((Δ.cornerL - p.l : ℤ) : ℝ) * Real.log 2) ≤ Δ.size := by
      simpa [TaoSection7Point.jReal, verticalDepth] using hweight
    linarith
  have hdiv :
      p.jReal - ((Δ.cornerJ : ℕ) : ℝ) ≤
        (Δ.size - (((Δ.cornerL - p.l : ℤ) : ℝ) * Real.log 2)) /
          Real.log 9 :=
    (le_div_iff₀' hlog9).2 (by simpa [mul_comm] using hmul)
  dsimp [rowRightEnd]
  linarith

theorem rowRightEnd_le_rowRightEnd_add_height_error
    {Δ : TaoSection7Triangle} {lLow lHigh : ℤ} {Lerr : ℝ}
    (hL : (lHigh : ℝ) - (lLow : ℝ) ≤ Lerr) :
    Δ.rowRightEnd lHigh ≤
      Δ.rowRightEnd lLow + (Real.log 2 / Real.log 9) * Lerr := by
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hcoeff_nonneg : 0 ≤ Real.log 2 / Real.log 9 :=
    (div_pos (Real.log_pos (by norm_num)) hlog9).le
  have hidentity :
      Δ.rowRightEnd lHigh =
        Δ.rowRightEnd lLow +
          (Real.log 2 / Real.log 9) * ((lHigh : ℝ) - (lLow : ℝ)) := by
    dsimp [rowRightEnd]
    rw [Int.cast_sub, Int.cast_sub]
    field_simp [ne_of_gt hlog9]
    ring
  rw [hidentity]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left (mul_le_mul_of_nonneg_left hL hcoeff_nonneg)
      (Δ.rowRightEnd lLow)

theorem exists_pnat_new_row_close_endpoint
    {new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {lStar : ℤ} {Lerr : ℝ}
    (hmem : new.Mem endpoint)
    (hlow : new.lowerTip ≤ (lStar : ℝ))
    (hle : (lStar : ℝ) ≤ endpoint.lReal)
    (hL : endpoint.lReal - (lStar : ℝ) ≤ Lerr) :
    ∃ jBridge : ℕ+,
      new.cornerJ ≤ jBridge ∧
        ((jBridge : ℕ) : ℝ) ≤ new.rowRightEnd lStar ∧
          lStar ≤ new.cornerL ∧
            |((jBridge : ℕ) : ℝ) - endpoint.jReal| ≤
              (Real.log 2 / Real.log 9) * Lerr + 1 := by
  have hrowCorner :
      ((new.cornerJ : ℕ) : ℝ) ≤ new.rowRightEnd lStar :=
    cornerJ_le_rowRightEnd_of_lowerTip_le hlow
  have hrowNonneg : 0 ≤ new.rowRightEnd lStar :=
    le_trans (Nat.cast_nonneg _) hrowCorner
  have hrowOne : (1 : ℝ) ≤ new.rowRightEnd lStar := by
    have hcorner_one : (1 : ℝ) ≤ ((new.cornerJ : ℕ) : ℝ) := by
      exact_mod_cast new.cornerJ.property
    exact le_trans hcorner_one hrowCorner
  have hl_endpoint_real : (lStar : ℝ) ≤ (endpoint.l : ℝ) := by
    simpa [TaoSection7Point.lReal] using hle
  have hl_endpoint_int : lStar ≤ endpoint.l := by
    exact_mod_cast hl_endpoint_real
  have hl_new : lStar ≤ new.cornerL :=
    le_trans hl_endpoint_int (mem_height_le hmem)
  have hL' : ((endpoint.l : ℝ) - (lStar : ℝ)) ≤ Lerr := by
    simpa [TaoSection7Point.lReal] using hL
  have hendpoint_le_low_row :
      endpoint.jReal ≤
        new.rowRightEnd lStar + (Real.log 2 / Real.log 9) * Lerr := by
    exact le_trans (jReal_le_rowRightEnd_of_mem hmem)
      (rowRightEnd_le_rowRightEnd_add_height_error
        (Δ := new) (lLow := lStar) (lHigh := endpoint.l) hL')
  by_cases hendpoint_row : endpoint.jReal ≤ new.rowRightEnd lStar
  · refine ⟨endpoint.j, mem_time_ge hmem, ?_, hl_new, ?_⟩
    · simpa [TaoSection7Point.jReal] using hendpoint_row
    · have hheight_nonneg :
          0 ≤ endpoint.lReal - (lStar : ℝ) := by
        linarith
      have hL_nonneg : 0 ≤ Lerr := le_trans hheight_nonneg hL
      have hcoeff_nonneg : 0 ≤ Real.log 2 / Real.log 9 :=
        (div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))).le
      have hzero :
          ((endpoint.j : ℕ) : ℝ) - endpoint.jReal = 0 := by
        dsimp [TaoSection7Point.jReal]
        ring
      rw [hzero, abs_zero]
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (by nlinarith [mul_nonneg hcoeff_nonneg hL_nonneg])
  · let nFloor : ℕ := Nat.floor (new.rowRightEnd lStar)
    have hcorner_floor_nat : (new.cornerJ : ℕ) ≤ nFloor := by
      exact Nat.le_floor hrowCorner
    have hfloor_pos : 0 < nFloor := by
      have hfloor_one : (1 : ℕ) ≤ nFloor := by
        exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ new.rowRightEnd lStar by
          simpa using hrowOne)
      omega
    refine ⟨⟨nFloor, hfloor_pos⟩, ?_, ?_, hl_new, ?_⟩
    · exact_mod_cast hcorner_floor_nat
    · simpa [nFloor] using Nat.floor_le hrowNonneg
    · have hfloor_le :
          ((nFloor : ℕ) : ℝ) ≤ new.rowRightEnd lStar := by
        simpa [nFloor] using Nat.floor_le hrowNonneg
      have hrow_lt_endpoint : new.rowRightEnd lStar < endpoint.jReal :=
        lt_of_not_ge hendpoint_row
      have hfloor_le_endpoint :
          ((nFloor : ℕ) : ℝ) ≤ endpoint.jReal :=
        le_trans hfloor_le hrow_lt_endpoint.le
      change |((nFloor : ℕ) : ℝ) - endpoint.jReal| ≤
        (Real.log 2 / Real.log 9) * Lerr + 1
      rw [abs_of_nonpos (sub_nonpos.mpr hfloor_le_endpoint)]
      have hrow_lt_floor_add_one :
          new.rowRightEnd lStar < ((nFloor + 1 : ℕ) : ℝ) := by
        simpa [nFloor] using
          (Nat.floor_lt hrowNonneg).1
            (Nat.lt_succ_self (Nat.floor (new.rowRightEnd lStar)))
      have hfloor_add_one :
          ((nFloor + 1 : ℕ) : ℝ) = ((nFloor : ℕ) : ℝ) + 1 := by
        norm_num
      linarith

theorem cornerJ_mem_rowJInterval_of_verticalDepth_log2_le_size
    {Γ : TaoSection7Triangle} {lStar : ℤ}
    (_hl : lStar ≤ Γ.cornerL)
    (hvert : ((Γ.cornerL - lStar : ℤ) : ℝ) * Real.log 2 ≤ Γ.size) :
    Γ.cornerJ ∈ Γ.rowJInterval lStar := by
  refine ⟨le_rfl, ?_⟩
  dsimp [rowJInterval, rowRightEnd]
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hnonneg :
      0 ≤ (Γ.size - ((Γ.cornerL - lStar : ℤ) : ℝ) * Real.log 2) / Real.log 9 := by
    exact div_nonneg (sub_nonneg.mpr hvert) (le_of_lt hlog9)
  linarith

theorem rowRightEnd_lt_cornerJ_of_disjoint_ordered
    {Δ Γ : TaoSection7Triangle} {lStar : ℤ}
    (hdisj : Disjoint (Δ.rowJInterval lStar) (Γ.rowJInterval lStar))
    (hordered : Δ.cornerJ ≤ Γ.cornerJ)
    (hΓleft : Γ.cornerJ ∈ Γ.rowJInterval lStar) :
    Δ.rowRightEnd lStar < ((Γ.cornerJ : ℕ) : ℝ) := by
  by_contra hnot
  have hle : ((Γ.cornerJ : ℕ) : ℝ) ≤ Δ.rowRightEnd lStar := le_of_not_gt hnot
  have hΓinΔ : Γ.cornerJ ∈ Δ.rowJInterval lStar := ⟨hordered, hle⟩
  exact (Set.disjoint_left.mp hdisj) hΓinΔ hΓleft

noncomputable def lemma710RowLevel (old : TaoSection7Triangle) (sMin : ℝ) : ℤ :=
  old.cornerL + Int.floor (sMin / 2)

theorem lemma710RowLevel_floor_bounds
    {old : TaoSection7Triangle} {sMin : ℝ} :
    (old.cornerL : ℝ) + sMin / 2 - 1 ≤
        ((lemma710RowLevel old sMin : ℤ) : ℝ) ∧
      ((lemma710RowLevel old sMin : ℤ) : ℝ) ≤
        (old.cornerL : ℝ) + sMin / 2 := by
  have hfloor_le : ((Int.floor (sMin / 2) : ℤ) : ℝ) ≤ sMin / 2 :=
    Int.floor_le (sMin / 2)
  have hfloor_lt : sMin / 2 < ((Int.floor (sMin / 2) : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one (sMin / 2)
  constructor
  · dsimp [lemma710RowLevel]
    rw [Int.cast_add]
    linarith
  · dsimp [lemma710RowLevel]
    rw [Int.cast_add]
    linarith

def lemma710LowerTipClose
    (K B : ℝ) (old Δ : TaoSection7Triangle) : Prop :=
  |Δ.lowerTip - (old.cornerL : ℝ)| ≤ K * B

theorem rowRightEnd_lower_bound_of_lowerTipClose
    {old Δ : TaoSection7Triangle} {sMin B K : ℝ}
    (_hB : 0 ≤ B) (_hK : 0 ≤ K)
    (hclose : lemma710LowerTipClose K B old Δ) :
    ((Δ.cornerJ : ℕ) : ℝ) +
        (Real.log 2 / Real.log 9) * (sMin / 2) -
        (Real.log 2 / Real.log 9) * (K * B + 1)
      ≤ Δ.rowRightEnd (lemma710RowLevel old sMin) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have halpha_nonneg : 0 ≤ Real.log 2 / Real.log 9 :=
    le_of_lt (div_pos hlog2 hlog9)
  have hfloor := (lemma710RowLevel_floor_bounds (old := old) (sMin := sMin)).1
  have htip_upper : Δ.lowerTip - (old.cornerL : ℝ) ≤ K * B :=
    (abs_le.mp hclose).2
  have hbase :
      sMin / 2 - (K * B + 1) ≤
        ((lemma710RowLevel old sMin : ℤ) : ℝ) - Δ.lowerTip := by
    linarith
  have hmul :
      (Real.log 2 / Real.log 9) * (sMin / 2 - (K * B + 1)) ≤
        (Real.log 2 / Real.log 9) *
          (((lemma710RowLevel old sMin : ℤ) : ℝ) - Δ.lowerTip) :=
    mul_le_mul_of_nonneg_left hbase halpha_nonneg
  rw [rowRightEnd_eq_cornerJ_add_lStar_sub_lowerTip]
  calc
    ((Δ.cornerJ : ℕ) : ℝ) +
          (Real.log 2 / Real.log 9) * (sMin / 2) -
          (Real.log 2 / Real.log 9) * (K * B + 1)
        =
        ((Δ.cornerJ : ℕ) : ℝ) +
          (Real.log 2 / Real.log 9) * (sMin / 2 - (K * B + 1)) := by
          ring
    _ ≤ ((Δ.cornerJ : ℕ) : ℝ) +
          (Real.log 2 / Real.log 9) *
            (((lemma710RowLevel old sMin : ℤ) : ℝ) - Δ.lowerTip) := by
          linarith
    _ = ((Δ.cornerJ : ℕ) : ℝ) +
          (((lemma710RowLevel old sMin : ℤ) : ℝ) - Δ.lowerTip) *
            Real.log 2 / Real.log 9 := by
          ring

def lemma710GapAbsorbs (K B sMin : ℝ) : Prop :=
  0 ≤ B ∧ 0 ≤ K ∧
    (Real.log 2 / Real.log 9) * (K * B + 1) ≤
      (Real.log 2 / (4 * Real.log 9)) * sMin

theorem lemma710GapAbsorbs_KB_add_one_le_quarter
    {sMin K B : ℝ}
    (habsorb : lemma710GapAbsorbs K B sMin) :
    K * B + 1 ≤ sMin / 4 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have halpha : 0 < Real.log 2 / Real.log 9 := div_pos hlog2 hlog9
  have hright :
      (Real.log 2 / (4 * Real.log 9)) * sMin =
        (Real.log 2 / Real.log 9) * (sMin / 4) := by
    have hlog9_ne : Real.log 9 ≠ 0 := ne_of_gt hlog9
    field_simp [hlog9_ne]
  have hmul :
      (Real.log 2 / Real.log 9) * (K * B + 1) ≤
        (Real.log 2 / Real.log 9) * (sMin / 4) := by
    simpa [hright] using habsorb.2.2
  exact le_of_mul_le_mul_left hmul halpha

theorem lemma710GapAbsorbs_sMin_nonneg
    {sMin K B : ℝ}
    (habsorb : lemma710GapAbsorbs K B sMin) :
    0 ≤ sMin := by
  have hquarter := lemma710GapAbsorbs_KB_add_one_le_quarter (sMin := sMin) habsorb
  have hKB : 0 ≤ K * B := mul_nonneg habsorb.2.1 habsorb.1
  nlinarith

theorem lemma710_lowerTip_le_rowLevel_of_lowerTipClose_gap
    {old Δ : TaoSection7Triangle} {sMin K B : ℝ}
    (hclose : lemma710LowerTipClose K B old Δ)
    (habsorb : lemma710GapAbsorbs K B sMin) :
    Δ.lowerTip ≤ ((lemma710RowLevel old sMin : ℤ) : ℝ) := by
  have hfloor := (lemma710RowLevel_floor_bounds (old := old) (sMin := sMin)).1
  have htip_upper : Δ.lowerTip - (old.cornerL : ℝ) ≤ K * B :=
    (abs_le.mp hclose).2
  have hquarter := lemma710GapAbsorbs_KB_add_one_le_quarter (sMin := sMin) habsorb
  have hs_nonneg := lemma710GapAbsorbs_sMin_nonneg (sMin := sMin) habsorb
  have hKB_le : K * B ≤ sMin / 2 - 1 := by
    nlinarith
  linarith

theorem lemma710_rowLevel_le_cornerL_of_size_ge_lowerTipClose_gap
    {old Δ : TaoSection7Triangle} {sMin K B : ℝ}
    (hsize : sMin ≤ Δ.size)
    (hclose : lemma710LowerTipClose K B old Δ)
    (habsorb : lemma710GapAbsorbs K B sMin) :
    lemma710RowLevel old sMin ≤ Δ.cornerL := by
  have hfloor := (lemma710RowLevel_floor_bounds (old := old) (sMin := sMin)).2
  have htip_lower : -(K * B) ≤ Δ.lowerTip - (old.cornerL : ℝ) :=
    (abs_le.mp hclose).1
  have hquarter := lemma710GapAbsorbs_KB_add_one_le_quarter (sMin := sMin) habsorb
  have hs_nonneg := lemma710GapAbsorbs_sMin_nonneg (sMin := sMin) habsorb
  have hKB_half : K * B ≤ sMin / 2 := by
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hsize_nonneg : 0 ≤ Δ.size := by
    linarith
  have hsize_le_div : Δ.size ≤ Δ.size / Real.log 2 := by
    have hmul : Δ.size * Real.log 2 ≤ Δ.size * 1 :=
      mul_le_mul_of_nonneg_left hlog2_le_one hsize_nonneg
    have hle : Real.log 2 * Δ.size ≤ Δ.size := by
      simpa [mul_comm] using hmul
    exact (le_div_iff₀' hlog2).2 hle
  have hs_div : sMin ≤ Δ.size / Real.log 2 := by
    linarith
  have hrow_real : ((lemma710RowLevel old sMin : ℤ) : ℝ) ≤ (Δ.cornerL : ℝ) := by
    dsimp [lowerTip] at htip_lower
    linarith
  exact Int.cast_le.mp hrow_real

theorem lemma710_rowLevel_verticalDepth_log2_le_size_of_lowerTipClose_gap
    {old Δ : TaoSection7Triangle} {sMin K B : ℝ}
    (hclose : lemma710LowerTipClose K B old Δ)
    (habsorb : lemma710GapAbsorbs K B sMin) :
    ((Δ.cornerL - lemma710RowLevel old sMin : ℤ) : ℝ) *
        Real.log 2 ≤ Δ.size := by
  have hrow_lower :=
    lemma710_lowerTip_le_rowLevel_of_lowerTipClose_gap
      (old := old) (Δ := Δ) (sMin := sMin) (K := K) (B := B)
      hclose habsorb
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase :
      ((Δ.cornerL - lemma710RowLevel old sMin : ℤ) : ℝ) ≤ Δ.size / Real.log 2 := by
    dsimp [lowerTip] at hrow_lower
    rw [Int.cast_sub]
    linarith
  have hmul := (le_div_iff₀' hlog2).mp hbase
  simpa [mul_comm] using hmul

theorem lemma710_cornerJ_mem_rowJInterval_of_size_ge_lowerTipClose_gap
    {old Δ : TaoSection7Triangle} {sMin K B : ℝ}
    (hsize : sMin ≤ Δ.size)
    (hclose : lemma710LowerTipClose K B old Δ)
    (habsorb : lemma710GapAbsorbs K B sMin) :
    Δ.cornerJ ∈ Δ.rowJInterval (lemma710RowLevel old sMin) := by
  exact cornerJ_mem_rowJInterval_of_verticalDepth_log2_le_size
    (lemma710_rowLevel_le_cornerL_of_size_ge_lowerTipClose_gap
      (old := old) (Δ := Δ) (sMin := sMin) (K := K) (B := B)
      hsize hclose habsorb)
    (lemma710_rowLevel_verticalDepth_log2_le_size_of_lowerTipClose_gap
      (old := old) (Δ := Δ) (sMin := sMin) (K := K) (B := B)
      hclose habsorb)

theorem cornerJ_gap_of_rowRightEnd_gap_and_scale
    {old Δ Γ : TaoSection7Triangle} {sMin B K : ℝ}
    (hrow : Δ.rowRightEnd (lemma710RowLevel old sMin) ≤
      ((Γ.cornerJ : ℕ) : ℝ))
    (hclose : lemma710LowerTipClose K B old Δ)
    (habsorb : lemma710GapAbsorbs K B sMin) :
    (Real.log 2 / (4 * Real.log 9)) * sMin ≤
      ((Γ.cornerJ : ℕ) : ℝ) - ((Δ.cornerJ : ℕ) : ℝ) := by
  have hlow :=
    rowRightEnd_lower_bound_of_lowerTipClose
      (old := old) (Δ := Δ) (sMin := sMin) (B := B) (K := K)
      habsorb.1 habsorb.2.1 hclose
  have hmain :
      ((Δ.cornerJ : ℕ) : ℝ) +
          (Real.log 2 / Real.log 9) * (sMin / 2) -
          (Real.log 2 / (4 * Real.log 9)) * sMin ≤
        ((Γ.cornerJ : ℕ) : ℝ) := by
    linarith [habsorb.2.2]
  have hcoeff :
      (Real.log 2 / Real.log 9) * (sMin / 2) -
          (Real.log 2 / (4 * Real.log 9)) * sMin =
        (Real.log 2 / (4 * Real.log 9)) * sMin := by
    have hlog9 : Real.log 9 ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    field_simp [hlog9]
    ring
  nlinarith [hmain, hcoeff]

def PointDisjoint (Δ Γ : TaoSection7Triangle) : Prop :=
  ∀ p : TaoSection7Point, Δ.Mem p → Γ.Mem p → False

theorem rowJInterval_disjoint_of_pointDisjoint
    {Δ Γ : TaoSection7Triangle} {lStar : ℤ}
    (hdisj : Δ.PointDisjoint Γ)
    (hΔ : lStar ≤ Δ.cornerL)
    (hΓ : lStar ≤ Γ.cornerL) :
    Disjoint (Δ.rowJInterval lStar) (Γ.rowJInterval lStar) := by
  rw [Set.disjoint_left]
  intro j hjΔ hjΓ
  exact hdisj ⟨j, lStar⟩
    (mem_of_mem_rowJInterval hjΔ hΔ)
    (mem_of_mem_rowJInterval hjΓ hΓ)

def SeparatedBy (r : ℝ) (Δ Γ : TaoSection7Triangle) : Prop :=
  ∀ p q : TaoSection7Point, Δ.Mem p → Γ.Mem q → r ^ 2 ≤ p.distSq q

def BlackOn (black : TaoSection7Point → Prop) (Δ : TaoSection7Triangle) : Prop :=
  ∀ p : TaoSection7Point, Δ.Mem p → black p

def Near (r : ℝ) (Δ : TaoSection7Triangle) (p : TaoSection7Point) : Prop :=
  ∃ q : TaoSection7Point, Δ.Mem q ∧ p.distSq q ≤ r ^ 2

def ClaimStar
    (black : TaoSection7Point → Prop) (r : ℝ) (Δ : TaoSection7Triangle) : Prop :=
  ∀ p : TaoSection7Point, ¬ Δ.Mem p → Δ.Near r p → ¬ black p

theorem ClaimStar.black_near_mem
    {black : TaoSection7Point → Prop} {r : ℝ} {Δ : TaoSection7Triangle}
    (hstar : Δ.ClaimStar black r) {p : TaoSection7Point}
    (hpblack : black p) (hpnear : Δ.Near r p) :
    Δ.Mem p := by
  by_contra hpnot
  exact (hstar p hpnot hpnear) hpblack

theorem separatedBy_of_claimStar_and_disjoint
    {black : TaoSection7Point → Prop} {r : ℝ} {Δ Γ : TaoSection7Triangle}
    (hstar : Δ.ClaimStar black r)
    (hΓblack : Γ.BlackOn black)
    (hdisj : Δ.PointDisjoint Γ) :
    Δ.SeparatedBy r Γ := by
  intro p q hp hq
  by_contra hnot
  have hlt : p.distSq q < r ^ 2 := not_le.mp hnot
  have hqnotΔ : ¬ Δ.Mem q := by
    intro hqΔ
    exact hdisj q hqΔ hq
  have hnear : Δ.Near r q := by
    refine ⟨p, hp, ?_⟩
    simpa [TaoSection7Point.distSq_comm] using le_of_lt hlt
  exact (hstar q hqnotΔ hnear) (hΓblack q hq)

end TaoSection7Triangle

def taoSection7TriangleLogScale (ε : ℝ) : ℝ :=
  Real.log (1 / ε)

def taoSection7TriangleSeparation (ε : ℝ) : ℝ :=
  (1 / 10 : ℝ) * taoSection7TriangleLogScale ε

def taoSection7TriangleRightBound (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ) / 2 - taoSection7TriangleSeparation ε

theorem taoSection7TriangleLogScale_nonneg
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ taoSection7TriangleLogScale ε := by
  unfold taoSection7TriangleLogScale
  have hone : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).mpr hε1
  exact Real.log_nonneg (by simpa [one_div] using hone)

theorem taoSection7TriangleSeparation_nonneg
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ taoSection7TriangleSeparation ε := by
  unfold taoSection7TriangleSeparation
  exact mul_nonneg (by norm_num) (taoSection7TriangleLogScale_nonneg hε0 hε1)

theorem taoSection7TriangleRightBound_le_half
    {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    taoSection7TriangleRightBound n ε ≤ (n : ℝ) / 2 := by
  unfold taoSection7TriangleRightBound
  have hsep := taoSection7TriangleSeparation_nonneg hε0 hε1
  linarith

def TaoSection7Black
    (ε : ℝ) (theta : TaoSection7Point → ℝ) (p : TaoSection7Point) : Prop :=
  |theta p| ≤ ε

def TaoSection7WeakBlack
    (theta : TaoSection7Point → ℝ) (p : TaoSection7Point) : Prop :=
  |theta p| ≤ (1 / 100 : ℝ)

theorem taoSection7Black_to_weak
    {ε : ℝ} {theta : TaoSection7Point → ℝ} {p : TaoSection7Point}
    (hε : ε ≤ (1 / 100 : ℝ))
    (hp : TaoSection7Black ε theta p) :
    TaoSection7WeakBlack theta p := by
  exact hp.trans hε

structure TaoSection7WeakBlackAdjacency
    (ε : ℝ) (theta : TaoSection7Point → ℝ) : Prop where
  claim_i_right :
    ∀ p : TaoSection7Point,
      TaoSection7WeakBlack theta p →
        TaoSection7Black ε theta p.right →
          TaoSection7Black ε theta p
  claim_i_down :
    ∀ p : TaoSection7Point,
      TaoSection7WeakBlack theta p →
        TaoSection7Black ε theta p.down →
          TaoSection7Black ε theta p
  claim_ii :
    ∀ p : TaoSection7Point,
      TaoSection7WeakBlack theta p.right →
        TaoSection7WeakBlack theta p.down →
          TaoSection7WeakBlack theta p
  claim_iii :
    ∀ (p : TaoSection7Point) (h : 1 < (p.j : ℕ)),
      TaoSection7WeakBlack theta (p.left h) →
        TaoSection7WeakBlack theta p.down →
          TaoSection7WeakBlack theta p

namespace TaoSection7WeakBlackAdjacency

end TaoSection7WeakBlackAdjacency

def TaoSection7TriangleFamilyPairwiseDisjoint
    (family : Set TaoSection7Triangle) : Prop :=
  ∀ ⦃Δ Γ : TaoSection7Triangle⦄,
    Δ ∈ family → Γ ∈ family → Δ ≠ Γ → Δ.PointDisjoint Γ

namespace TaoSection7TriangleFamilyPairwiseDisjoint

theorem no_common_mem
    {family : Set TaoSection7Triangle} {Δ Γ : TaoSection7Triangle}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hΔ : Δ ∈ family) (hΓ : Γ ∈ family) (hne : Δ ≠ Γ)
    {p : TaoSection7Point} :
    Δ.Mem p → Γ.Mem p → False :=
  hpair hΔ hΓ hne p

end TaoSection7TriangleFamilyPairwiseDisjoint

namespace TaoSection7Triangle

theorem rowJInterval_disjoint_of_familyPairwiseDisjoint
    {family : Set TaoSection7Triangle} {Δ Γ : TaoSection7Triangle} {lStar : ℤ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hΔmem : Δ ∈ family) (hΓmem : Γ ∈ family)
    (hne : Δ ≠ Γ)
    (hΔrow : lStar ≤ Δ.cornerL) (hΓrow : lStar ≤ Γ.cornerL) :
    Disjoint (Δ.rowJInterval lStar) (Γ.rowJInterval lStar) :=
  rowJInterval_disjoint_of_pointDisjoint (hpair hΔmem hΓmem hne) hΔrow hΓrow

end TaoSection7Triangle

namespace TaoSection7Lemma710

def anchor (old Δ : TaoSection7Triangle) : TaoSection7Point :=
  ⟨Δ.cornerJ, old.cornerL⟩

structure Center
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (sMin K B : ℝ) where
  triangle : TaoSection7Triangle
  mem_family : triangle ∈ family
  lowerTipClose : TaoSection7Triangle.lemma710LowerTipClose K B old triangle
  size_ge : sMin ≤ triangle.size

namespace Center

def point
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (c : Center family old sMin K B) : TaoSection7Point :=
  anchor old c.triangle

@[simp] theorem point_l
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (c : Center family old sMin K B) :
    c.point.l = old.cornerL :=
  rfl

theorem rowLevel_le_cornerL
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (c : Center family old sMin K B)
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin) :
    TaoSection7Triangle.lemma710RowLevel old sMin ≤ c.triangle.cornerL :=
  TaoSection7Triangle.lemma710_rowLevel_le_cornerL_of_size_ge_lowerTipClose_gap
    c.size_ge c.lowerTipClose habsorb

theorem cornerJ_mem_rowJInterval
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (c : Center family old sMin K B)
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin) :
    c.triangle.cornerJ ∈
      c.triangle.rowJInterval (TaoSection7Triangle.lemma710RowLevel old sMin) :=
  TaoSection7Triangle.lemma710_cornerJ_mem_rowJInterval_of_size_ge_lowerTipClose_gap
    c.size_ge c.lowerTipClose habsorb

end Center

def Sigma
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (sMin K B : ℝ) :
    Set TaoSection7Point :=
  Set.range (fun c : Center family old sMin K B => c.point)

theorem center_mem_sigma
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (c : Center family old sMin K B) :
    c.point ∈ Sigma family old sMin K B :=
  ⟨c, rfl⟩

theorem sigma_same_horizontal
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    {p : TaoSection7Point}
    (hp : p ∈ Sigma family old sMin K B) :
    p.l = old.cornerL := by
  rcases hp with ⟨c, rfl⟩
  rfl

def NearSigma (r : ℝ) (Sigma : Set TaoSection7Point) (p : TaoSection7Point) : Prop :=
  ∃ q : TaoSection7Point, q ∈ Sigma ∧ p.distSq q ≤ r ^ 2

theorem nearSigma_of_near_anchor
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B r : ℝ}
    (c : Center family old sMin K B) {p : TaoSection7Point}
    (hp : p.distSq c.point ≤ r ^ 2) :
    NearSigma r (Sigma family old sMin K B) p :=
  ⟨c.point, center_mem_sigma c, hp⟩

def LowTipCommonPointBridge
    (old new : TaoSection7Triangle) (gap : ℝ) : Prop :=
  new.lowerTip < (old.cornerL : ℝ) - gap →
    ∃ p : TaoSection7Point, old.Mem p ∧ new.Mem p

def LowTipRowCommonPointBridge
    (old new : TaoSection7Triangle) (gap : ℝ) : Prop :=
  new.lowerTip < (old.cornerL : ℝ) - gap →
    ∃ jBridge : ℕ+,
      old.Mem ⟨jBridge, old.cornerL⟩ ∧
        new.Mem ⟨jBridge, old.cornerL⟩

theorem lemma710_log_margin_pos :
    0 < Real.log 2 / Real.log 9 - (1 / 4 : ℝ) := by
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num : (1 : ℝ) < 9)
  have hlog9_lt : Real.log 9 < 4 * Real.log 2 := by
    have hlt : Real.log (9 : ℝ) < Real.log (16 : ℝ) :=
      Real.log_lt_log (by norm_num : (0 : ℝ) < 9) (by norm_num : (9 : ℝ) < 16)
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
      rw [Real.log_pow]
      norm_num
    linarith
  have hquarter_lt : (1 / 4 : ℝ) < Real.log 2 / Real.log 9 := by
    rw [lt_div_iff₀ hlog9]
    nlinarith
  linarith

theorem lemma710_log_margin_le_quarter :
    Real.log 2 / Real.log 9 - (1 / 4 : ℝ) ≤ 1 / 4 := by
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num : (1 : ℝ) < 9)
  have hlog2_le : 2 * Real.log 2 ≤ Real.log 9 := by
    have hle : Real.log (4 : ℝ) ≤ Real.log (9 : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 9)
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      rw [Real.log_pow]
      norm_num
    linarith
  have hhalf : Real.log 2 / Real.log 9 ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hlog9]
    nlinarith
  linarith

theorem lemma710_oldRowBudgets_of_error_margin
    {S Lerr Jerr : ℝ}
    (hS : 0 ≤ S)
    (hE :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤ S / 4 ∧
      (Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1)) * Real.log 9 ≤
        S * (Real.log 2 - Real.log 9 / 4) := by
  constructor
  · have hmul :=
      mul_le_mul_of_nonneg_left lemma710_log_margin_le_quarter hS
    linarith
  · have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num : (1 : ℝ) < 9)
    have hmul := mul_le_mul_of_nonneg_right hE hlog9.le
    have hid :
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) * Real.log 9 =
          S * (Real.log 2 - Real.log 9 / 4) := by
      field_simp [ne_of_gt hlog9]
    nlinarith

theorem lowTipCommonPointBridge_of_rowCommonPointBridge
    {old new : TaoSection7Triangle} {gap : ℝ}
    (hbridge : LowTipRowCommonPointBridge old new gap) :
    LowTipCommonPointBridge old new gap := by
  intro hbad
  rcases hbridge hbad with ⟨jBridge, hmem_old, hmem_new⟩
  exact ⟨⟨jBridge, old.cornerL⟩, hmem_old, hmem_new⟩

theorem lowTipRowCommonPointBridge_of_bad_row_bounds
    {old new : TaoSection7Triangle} {gap : ℝ}
    (hrow :
      new.lowerTip < (old.cornerL : ℝ) - gap →
        ∃ jBridge : ℕ+,
          old.cornerJ ≤ jBridge ∧
            ((jBridge : ℕ) : ℝ) ≤ old.rowRightEnd old.cornerL ∧
              new.cornerJ ≤ jBridge ∧
                ((jBridge : ℕ) : ℝ) ≤ new.rowRightEnd old.cornerL ∧
                  old.cornerL ≤ new.cornerL) :
    LowTipRowCommonPointBridge old new gap := by
  intro hbad
  rcases hrow hbad with
    ⟨jBridge, hOldLeft, hOldRight, hNewLeft, hNewRight, hNewRow⟩
  exact
    ⟨jBridge,
      TaoSection7Triangle.mem_of_row_bounds hOldLeft hOldRight le_rfl,
      TaoSection7Triangle.mem_of_row_bounds hNewLeft hNewRight hNewRow⟩

structure OutsideEprimeBadLowerTipRowData
    (old new : TaoSection7Triangle)
    (base endpoint : TaoSection7Point)
    (S Lerr Jerr gap : ℝ) : Prop where
  base_mem_old : old.Mem base
  endpoint_mem_new : new.Mem endpoint
  s_def : S = ((old.cornerL - base.l : ℤ) : ℝ)
  endpoint_l_lower : (old.cornerL : ℝ) ≤ endpoint.lReal
  endpoint_l_upper : endpoint.lReal - (old.cornerL : ℝ) ≤ Lerr
  endpoint_j_close : |endpoint.jReal - (base.jReal + S / 4)| ≤ Jerr
  gap_nonneg : 0 ≤ gap
  Lerr_nonneg : 0 ≤ Lerr
  Jerr_nonneg : 0 ≤ Jerr
  old_left_budget :
    Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤ S / 4
  old_right_budget :
    (Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1)) * Real.log 9
      ≤ S * (Real.log 2 - Real.log 9 / 4)

theorem outsideEprimeBadLowerTipRowData_of_endpoint_estimates
    {old new : TaoSection7Triangle}
    {base endpoint : TaoSection7Point}
    {S Lerr Jerr gap : ℝ}
    (hbase : old.Mem base)
    (hendpoint : new.Mem endpoint)
    (hS : S = ((old.cornerL - base.l : ℤ) : ℝ))
    (hlower : (old.cornerL : ℝ) ≤ endpoint.lReal)
    (hupper : endpoint.lReal - (old.cornerL : ℝ) ≤ Lerr)
    (hj : |endpoint.jReal - (base.jReal + S / 4)| ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hL0 : 0 ≤ Lerr)
    (hJ0 : 0 ≤ Jerr)
    (hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    OutsideEprimeBadLowerTipRowData old new base endpoint S Lerr Jerr gap := by
  have hheight : base.l ≤ old.cornerL :=
    TaoSection7Triangle.mem_height_le hbase
  have hS_nonneg_raw : 0 ≤ (((old.cornerL - base.l : ℤ) : ℝ)) := by
    have hint : 0 ≤ old.cornerL - base.l := sub_nonneg.mpr hheight
    exact_mod_cast hint
  have hS_nonneg : 0 ≤ S := by
    simpa [hS] using hS_nonneg_raw
  have hbudgets :=
    lemma710_oldRowBudgets_of_error_margin hS_nonneg hmargin
  exact
    { base_mem_old := hbase
      endpoint_mem_new := hendpoint
      s_def := hS
      endpoint_l_lower := hlower
      endpoint_l_upper := hupper
      endpoint_j_close := hj
      gap_nonneg := hgap0
      Lerr_nonneg := hL0
      Jerr_nonneg := hJ0
      old_left_budget := hbudgets.1
      old_right_budget := hbudgets.2 }

theorem outsideEprimeBadLowerTip_rowBounds
    {old new : TaoSection7Triangle}
    {base endpoint : TaoSection7Point}
    {S Lerr Jerr gap : ℝ}
    (hdata :
      OutsideEprimeBadLowerTipRowData old new base endpoint S Lerr Jerr gap)
    (hbad : new.lowerTip < (old.cornerL : ℝ) - gap) :
    ∃ jBridge : ℕ+,
      old.cornerJ ≤ jBridge ∧
        ((jBridge : ℕ) : ℝ) ≤ old.rowRightEnd old.cornerL ∧
          new.cornerJ ≤ jBridge ∧
            ((jBridge : ℕ) : ℝ) ≤ new.rowRightEnd old.cornerL ∧
              old.cornerL ≤ new.cornerL := by
  let Rerr : ℝ := (Real.log 2 / Real.log 9) * Lerr + 1
  let E : ℝ := Jerr + Rerr
  have hnew_low : new.lowerTip ≤ (old.cornerL : ℝ) := by
    linarith [hdata.gap_nonneg]
  rcases TaoSection7Triangle.exists_pnat_new_row_close_endpoint
      (new := new) (endpoint := endpoint) (lStar := old.cornerL)
      (Lerr := Lerr) hdata.endpoint_mem_new hnew_low
      hdata.endpoint_l_lower hdata.endpoint_l_upper with
    ⟨jBridge, hNewLeft, hNewRight, hNewRow, hround⟩
  have hround_lower :
      -Rerr ≤ ((jBridge : ℕ) : ℝ) - endpoint.jReal := by
    simpa [Rerr] using (abs_le.mp hround).1
  have hround_upper :
      ((jBridge : ℕ) : ℝ) - endpoint.jReal ≤ Rerr := by
    simpa [Rerr] using (abs_le.mp hround).2
  have hend_lower :
      -Jerr ≤ endpoint.jReal - (base.jReal + S / 4) :=
    (abs_le.mp hdata.endpoint_j_close).1
  have hend_upper :
      endpoint.jReal - (base.jReal + S / 4) ≤ Jerr :=
    (abs_le.mp hdata.endpoint_j_close).2
  have hbase_le_bridge_real :
      base.jReal ≤ ((jBridge : ℕ) : ℝ) := by
    have hleft : E ≤ S / 4 := by
      simpa [E, Rerr] using hdata.old_left_budget
    linarith
  have hbase_le_bridge : base.j ≤ jBridge := by
    exact_mod_cast
      (by
        simpa [TaoSection7Point.jReal] using hbase_le_bridge_real :
          ((base.j : ℕ) : ℝ) ≤ ((jBridge : ℕ) : ℝ))
  have hOldLeft : old.cornerJ ≤ jBridge :=
    le_trans (TaoSection7Triangle.mem_time_ge hdata.base_mem_old) hbase_le_bridge
  have hbridge_upper_center :
      ((jBridge : ℕ) : ℝ) ≤ base.jReal + S / 4 + E := by
    linarith
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hlog9_nonneg : 0 ≤ Real.log 9 := hlog9.le
  have hbase_corner := TaoSection7Triangle.mem_time_ge hdata.base_mem_old
  have hbase_depth :=
    TaoSection7Triangle.horizontalDepth_real_eq_sub_of_cornerJ_le
      (Δ := old) (jStar := base.j) (lStar := base.l) hbase_corner
  have hbase_weight := TaoSection7Triangle.mem_weight_le_size hdata.base_mem_old
  have hbase_weight' :
      (base.jReal - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 +
          S * Real.log 2 ≤ old.size := by
    rw [hbase_depth] at hbase_weight
    simpa [TaoSection7Point.jReal, TaoSection7Triangle.verticalDepth, ← hdata.s_def]
      using hbase_weight
  have hbudget_sum :
      (S / 4 + E) * Real.log 9 ≤ S * Real.log 2 := by
    have hbudget : E * Real.log 9 ≤ S * (Real.log 2 - Real.log 9 / 4) := by
      simpa [E, Rerr] using hdata.old_right_budget
    nlinarith
  have hbridge_delta_le :
      (((jBridge : ℕ) : ℝ) - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 ≤
        (base.jReal - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 + S * Real.log 2 := by
    have hdelta :
        ((jBridge : ℕ) : ℝ) - ((old.cornerJ : ℕ) : ℝ) ≤
          (base.jReal - ((old.cornerJ : ℕ) : ℝ)) + (S / 4 + E) := by
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_right hdelta hlog9_nonneg
    nlinarith
  have hbridge_weight :
      (((jBridge : ℕ) : ℝ) - ((old.cornerJ : ℕ) : ℝ)) * Real.log 9 ≤
        old.size :=
    le_trans hbridge_delta_le hbase_weight'
  have hbridge_div :
      ((jBridge : ℕ) : ℝ) - ((old.cornerJ : ℕ) : ℝ) ≤ old.size / Real.log 9 :=
    (le_div_iff₀' hlog9).2 (by simpa [mul_comm] using hbridge_weight)
  have hOldRight :
      ((jBridge : ℕ) : ℝ) ≤ old.rowRightEnd old.cornerL := by
    dsimp [TaoSection7Triangle.rowRightEnd]
    simp
    linarith
  exact ⟨jBridge, hOldLeft, hOldRight, hNewLeft, hNewRight, hNewRow⟩

theorem lowTipRowCommonPointBridge_of_outsideEprimeBadLowerTipRowData
    {old new : TaoSection7Triangle}
    {base endpoint : TaoSection7Point}
    {S Lerr Jerr gap : ℝ}
    (hdata :
      OutsideEprimeBadLowerTipRowData old new base endpoint S Lerr Jerr gap) :
    LowTipRowCommonPointBridge old new gap :=
  lowTipRowCommonPointBridge_of_bad_row_bounds
    (fun hbad => outsideEprimeBadLowerTip_rowBounds hdata hbad)

theorem lowerTip_lower_bound_of_commonPointBridge
    {family : Set TaoSection7Triangle} {old new : TaoSection7Triangle}
    {gap : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family) (hnew : new ∈ family) (hne : new ≠ old)
    (hbridge : LowTipCommonPointBridge old new gap) :
    (old.cornerL : ℝ) - gap ≤ new.lowerTip := by
  by_contra hnot
  have hlt : new.lowerTip < (old.cornerL : ℝ) - gap := lt_of_not_ge hnot
  rcases hbridge hlt with ⟨p, hmem_old, hmem_new⟩
  exact TaoSection7TriangleFamilyPairwiseDisjoint.no_common_mem
    hpair hold hnew (by intro h; exact hne h.symm)
    hmem_old hmem_new

theorem lowerTip_lower_bound_of_commonPointBridge_absorb
    {family : Set TaoSection7Triangle} {old new : TaoSection7Triangle}
    {gap K B : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family) (hnew : new ∈ family) (hne : new ≠ old)
    (hgap : gap ≤ K * B)
    (hbridge : LowTipCommonPointBridge old new gap) :
    (old.cornerL : ℝ) - K * B ≤ new.lowerTip := by
  have hlow :
      (old.cornerL : ℝ) - gap ≤ new.lowerTip :=
    lowerTip_lower_bound_of_commonPointBridge
      hpair hold hnew hne hbridge
  linarith

theorem lowerTipClose_of_endpoint_and_bridge
    {old new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {K B : ℝ}
    (hend : new.Mem endpoint)
    (hend_l : endpoint.lReal - (old.cornerL : ℝ) ≤ K * B)
    (hlow : (old.cornerL : ℝ) - K * B ≤ new.lowerTip) :
    TaoSection7Triangle.lemma710LowerTipClose K B old new := by
  have htip_le_endpoint :=
    TaoSection7Triangle.lowerTip_le_lReal_of_mem hend
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem distSq_anchor_le_of_coord_bounds
    {old new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {Rj Rl R : ℝ}
    (hj : |endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)| ≤ Rj)
    (hl : |endpoint.lReal - (old.cornerL : ℝ)| ≤ Rl)
    (hquad : Rj ^ 2 + Rl ^ 2 ≤ R ^ 2) :
    endpoint.distSq (anchor old new) ≤ R ^ 2 := by
  have hj_bounds := abs_le.mp hj
  have hl_bounds := abs_le.mp hl
  have hj_sq :
      (endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)) ^ 2 ≤ Rj ^ 2 := by
    nlinarith
  have hl_sq :
      (endpoint.lReal - (old.cornerL : ℝ)) ^ 2 ≤ Rl ^ 2 := by
    nlinarith
  have hsum :
      (endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)) ^ 2 +
          (endpoint.lReal - (old.cornerL : ℝ)) ^ 2 ≤ R ^ 2 := by
    nlinarith
  simpa [TaoSection7Point.distSq, TaoSection7Point.jReal,
    TaoSection7Point.lReal, anchor] using hsum

theorem anchorJClose_of_mem_lowerTipClose_lClose
    {old new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {Ltip Lend J : ℝ}
    (hmem : new.Mem endpoint)
    (hlow : |new.lowerTip - (old.cornerL : ℝ)| ≤ Ltip)
    (hend : |endpoint.lReal - (old.cornerL : ℝ)| ≤ Lend)
    (hJ : (Real.log 2 / Real.log 9) * (Ltip + Lend) ≤ J) :
    |endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)| ≤ J := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hcoeff_nonneg : 0 ≤ Real.log 2 / Real.log 9 :=
    (div_pos hlog2 hlog9).le
  have hcorner := TaoSection7Triangle.mem_time_ge hmem
  have hj_nonneg : 0 ≤ endpoint.jReal - ((new.cornerJ : ℕ) : ℝ) := by
    dsimp [TaoSection7Point.jReal]
    exact sub_nonneg.mpr (by exact_mod_cast hcorner)
  have hhor_eq :=
    TaoSection7Triangle.horizontalDepth_real_eq_sub_of_cornerJ_le
      (Δ := new) (jStar := endpoint.j) (lStar := endpoint.l) hcorner
  have hweight := TaoSection7Triangle.mem_weight_le_size hmem
  have hweight' :
      (endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)) * Real.log 9 +
          ((new.verticalDepth endpoint : ℤ) : ℝ) * Real.log 2 ≤ new.size := by
    simpa [TaoSection7Point.jReal, hhor_eq] using hweight
  have hidentity :
      new.size - ((new.verticalDepth endpoint : ℤ) : ℝ) * Real.log 2 =
        (endpoint.lReal - new.lowerTip) * Real.log 2 := by
    dsimp [TaoSection7Triangle.verticalDepth, TaoSection7Triangle.lowerTip,
      TaoSection7Point.lReal]
    rw [Int.cast_sub]
    field_simp [ne_of_gt hlog2]
    ring
  have hhor_log :
      (endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)) * Real.log 9 ≤
        (endpoint.lReal - new.lowerTip) * Real.log 2 := by
    linarith
  have hj_le_raw :
      endpoint.jReal - ((new.cornerJ : ℕ) : ℝ) ≤
        ((endpoint.lReal - new.lowerTip) * Real.log 2) / Real.log 9 :=
    (le_div_iff₀' hlog9).2 (by simpa [mul_comm] using hhor_log)
  have hraw_eq :
      ((endpoint.lReal - new.lowerTip) * Real.log 2) / Real.log 9 =
        (Real.log 2 / Real.log 9) * (endpoint.lReal - new.lowerTip) := by
    field_simp [ne_of_gt hlog9]
  have hend_upper : endpoint.lReal - (old.cornerL : ℝ) ≤ Lend :=
    (abs_le.mp hend).2
  have hlow_lower : -(Ltip) ≤ new.lowerTip - (old.cornerL : ℝ) :=
    (abs_le.mp hlow).1
  have hheight :
      endpoint.lReal - new.lowerTip ≤ Ltip + Lend := by
    linarith
  have hj_le_scale :
      endpoint.jReal - ((new.cornerJ : ℕ) : ℝ) ≤
        (Real.log 2 / Real.log 9) * (Ltip + Lend) := by
    rw [hraw_eq] at hj_le_raw
    exact le_trans hj_le_raw
      (mul_le_mul_of_nonneg_left hheight hcoeff_nonneg)
  exact abs_le.mpr ⟨by linarith, le_trans hj_le_scale hJ⟩

structure RawOutsideEprimeCommonPointEndpointData
    (old new : TaoSection7Triangle) (endpoint : TaoSection7Point)
    (gap K B : ℝ) where
  endpoint_mem : new.Mem endpoint
  lower_common_bridge : LowTipCommonPointBridge old new gap
  gap_le : gap ≤ K * B
  l_close : |endpoint.lReal - (old.cornerL : ℝ)| ≤ K * B

theorem rawOutsideEprimeCommonPointEndpointData_of_rowData
    {old new : TaoSection7Triangle} {base endpoint : TaoSection7Point}
    {S Lerr Jerr gap K B : ℝ}
    (hdata :
      OutsideEprimeBadLowerTipRowData old new base endpoint S Lerr Jerr gap)
    (hgap : gap ≤ K * B)
    (hLerr : Lerr ≤ K * B) :
    RawOutsideEprimeCommonPointEndpointData old new endpoint gap K B := by
  have hrowBridge :
      LowTipRowCommonPointBridge old new gap :=
    lowTipRowCommonPointBridge_of_outsideEprimeBadLowerTipRowData hdata
  have hcommon :
      LowTipCommonPointBridge old new gap :=
    lowTipCommonPointBridge_of_rowCommonPointBridge hrowBridge
  have hKB_nonneg : 0 ≤ K * B := le_trans hdata.Lerr_nonneg hLerr
  have hlower :
      -(K * B) ≤ endpoint.lReal - (old.cornerL : ℝ) := by
    have hdiff_nonneg :
        0 ≤ endpoint.lReal - (old.cornerL : ℝ) := by
      linarith [hdata.endpoint_l_lower]
    linarith
  have hupper :
      endpoint.lReal - (old.cornerL : ℝ) ≤ K * B :=
    le_trans hdata.endpoint_l_upper hLerr
  exact
    { endpoint_mem := hdata.endpoint_mem_new
      lower_common_bridge := hcommon
      gap_le := hgap
      l_close := abs_le.mpr ⟨hlower, hupper⟩ }

theorem rawOutsideEprimeCommonPointEndpointData_to_center_nearSigma
    {family : Set TaoSection7Triangle}
    {old new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {sMin gap K B J R : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family) (hnew : new ∈ family) (hne : new ≠ old)
    (hsize : sMin ≤ new.size)
    (hJ : (Real.log 2 / Real.log 9) * (K * B + K * B) ≤ J)
    (hradius : J ^ 2 + (K * B) ^ 2 ≤ R ^ 2)
    (hdata : RawOutsideEprimeCommonPointEndpointData old new endpoint gap K B) :
    ∃ c : Center family old sMin K B,
      c.triangle = new ∧
        NearSigma R (Sigma family old sMin K B) endpoint := by
  have hlow :=
    lowerTip_lower_bound_of_commonPointBridge_absorb
      hpair hold hnew hne hdata.gap_le hdata.lower_common_bridge
  have hend_l : endpoint.lReal - (old.cornerL : ℝ) ≤ K * B :=
    (abs_le.mp hdata.l_close).2
  have hclose :
      TaoSection7Triangle.lemma710LowerTipClose K B old new :=
    lowerTipClose_of_endpoint_and_bridge hdata.endpoint_mem hend_l hlow
  have hj_close :
      |endpoint.jReal - ((new.cornerJ : ℕ) : ℝ)| ≤ J :=
    anchorJClose_of_mem_lowerTipClose_lClose
      hdata.endpoint_mem hclose hdata.l_close hJ
  let c : Center family old sMin K B :=
    { triangle := new
      mem_family := hnew
      lowerTipClose := hclose
      size_ge := hsize }
  have hdist :
      endpoint.distSq (anchor old new) ≤ R ^ 2 :=
    distSq_anchor_le_of_coord_bounds
      hj_close hdata.l_close hradius
  refine ⟨c, rfl, ?_⟩
  exact nearSigma_of_near_anchor c (by simpa [c, Center.point] using hdist)

theorem center_j_gap_of_pairwiseDisjoint
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin B K : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (c d : Center family old sMin K B)
    (hne : c.triangle ≠ d.triangle)
    (hordered : c.triangle.cornerJ ≤ d.triangle.cornerJ)
    (hcrow : TaoSection7Triangle.lemma710RowLevel old sMin ≤ c.triangle.cornerL)
    (hdrow : TaoSection7Triangle.lemma710RowLevel old sMin ≤ d.triangle.cornerL)
    (hdleft :
      d.triangle.cornerJ ∈
        d.triangle.rowJInterval (TaoSection7Triangle.lemma710RowLevel old sMin))
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin) :
    (Real.log 2 / (4 * Real.log 9)) * sMin ≤
      ((d.point.j : ℕ) : ℝ) - ((c.point.j : ℕ) : ℝ) := by
  have hrows :
      Disjoint
        (c.triangle.rowJInterval (TaoSection7Triangle.lemma710RowLevel old sMin))
        (d.triangle.rowJInterval (TaoSection7Triangle.lemma710RowLevel old sMin)) :=
    TaoSection7Triangle.rowJInterval_disjoint_of_familyPairwiseDisjoint
      hpair c.mem_family d.mem_family hne hcrow hdrow
  have hlt :
      c.triangle.rowRightEnd (TaoSection7Triangle.lemma710RowLevel old sMin) <
        ((d.triangle.cornerJ : ℕ) : ℝ) :=
    TaoSection7Triangle.rowRightEnd_lt_cornerJ_of_disjoint_ordered
      hrows hordered hdleft
  have hgap :=
    TaoSection7Triangle.cornerJ_gap_of_rowRightEnd_gap_and_scale
      (old := old) (Δ := c.triangle) (Γ := d.triangle)
      (sMin := sMin) (B := B) (K := K)
      (le_of_lt hlt) c.lowerTipClose habsorb
  simpa [Center.point] using hgap

theorem center_j_gap_of_pairwiseDisjoint_autoRows
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (c d : Center family old sMin K B)
    (hne : c.triangle ≠ d.triangle)
    (hordered : c.triangle.cornerJ ≤ d.triangle.cornerJ)
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin) :
    (Real.log 2 / (4 * Real.log 9)) * sMin ≤
      ((d.point.j : ℕ) : ℝ) - ((c.point.j : ℕ) : ℝ) := by
  exact center_j_gap_of_pairwiseDisjoint
    (sMin := sMin) (B := B) (K := K)
    hpair c d hne hordered
    (Center.rowLevel_le_cornerL c habsorb)
    (Center.rowLevel_le_cornerL d habsorb)
    (Center.cornerJ_mem_rowJInterval d habsorb)
    habsorb

theorem separationScale_nonneg_of_gapAbsorbs
    {sMin K B : ℝ}
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin) :
    0 ≤ (Real.log 2 / (4 * Real.log 9)) * sMin := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hcoeff : 0 ≤ Real.log 2 / (4 * Real.log 9) :=
    (div_pos hlog2 (mul_pos (by norm_num) hlog9)).le
  exact mul_nonneg hcoeff
    (TaoSection7Triangle.lemma710GapAbsorbs_sMin_nonneg
      (sMin := sMin) habsorb)

theorem sigma_distSq_ge_of_pairwiseDisjoint_autoRows
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin)
    {p q : TaoSection7Point}
    (hp : p ∈ Sigma family old sMin K B)
    (hq : q ∈ Sigma family old sMin K B)
    (hpq : p ≠ q) :
    ((Real.log 2 / (4 * Real.log 9)) * sMin) ^ 2 ≤ p.distSq q := by
  rcases hp with ⟨c, rfl⟩
  rcases hq with ⟨d, rfl⟩
  have hne : c.triangle ≠ d.triangle := by
    intro htri
    apply hpq
    simp [Center.point, anchor, htri]
  have hsep_nonneg :=
    separationScale_nonneg_of_gapAbsorbs
      (sMin := sMin) (K := K) (B := B) habsorb
  by_cases hordered : c.triangle.cornerJ ≤ d.triangle.cornerJ
  · have hgap :=
      center_j_gap_of_pairwiseDisjoint_autoRows
        hpair c d hne hordered habsorb
    have hdist :
        c.point.distSq d.point =
          (((d.point.j : ℕ) : ℝ) - ((c.point.j : ℕ) : ℝ)) ^ 2 := by
      dsimp [TaoSection7Point.distSq, TaoSection7Point.jReal, TaoSection7Point.lReal]
      simp
      ring
    rw [hdist]
    nlinarith
  · have hordered' : d.triangle.cornerJ ≤ c.triangle.cornerJ :=
      le_of_lt (lt_of_not_ge hordered)
    have hgap :=
      center_j_gap_of_pairwiseDisjoint_autoRows
        hpair d c hne.symm hordered' habsorb
    have hdist :
        c.point.distSq d.point =
          (((c.point.j : ℕ) : ℝ) - ((d.point.j : ℕ) : ℝ)) ^ 2 := by
      dsimp [TaoSection7Point.distSq, TaoSection7Point.jReal, TaoSection7Point.lReal]
      simp
    rw [hdist]
    nlinarith

end TaoSection7Lemma710

def TaoSection7TriangleFamilySeparatedBy
    (r : ℝ) (family : Set TaoSection7Triangle) : Prop :=
  ∀ ⦃Δ Γ : TaoSection7Triangle⦄,
    Δ ∈ family → Γ ∈ family → Δ ≠ Γ → Δ.SeparatedBy r Γ

def TaoSection7TriangleFamilyInStrip
    (rightBound : ℝ) (family : Set TaoSection7Triangle) : Prop :=
  ∀ ⦃Δ : TaoSection7Triangle⦄, Δ ∈ family →
    ∀ ⦃p : TaoSection7Point⦄, Δ.Mem p → ((p.j : ℕ) : ℝ) ≤ rightBound

def TaoSection7TriangleRightEdgeInStrip
    (rightBound : ℝ) (Δ : TaoSection7Triangle) : Prop :=
  ((Δ.cornerJ : ℕ) : ℝ) + Δ.size / Real.log 9 ≤ rightBound

def TaoSection7TriangleFamilyRightEdgeInStrip
    (rightBound : ℝ) (family : Set TaoSection7Triangle) : Prop :=
  ∀ ⦃Δ : TaoSection7Triangle⦄, Δ ∈ family →
    TaoSection7TriangleRightEdgeInStrip rightBound Δ

def TaoSection7TriangleFamilyCoverBlack
    (black : TaoSection7Point → Prop) (family : Set TaoSection7Triangle) : Prop :=
  ∀ p : TaoSection7Point, black p ↔ ∃ Δ ∈ family, Δ.Mem p

def TaoSection7TriangleFamilyBlackOn
    (black : TaoSection7Point → Prop) (family : Set TaoSection7Triangle) : Prop :=
  ∀ ⦃Δ : TaoSection7Triangle⦄, Δ ∈ family → Δ.BlackOn black

def TaoSection7TriangleFamilyClaimStar
    (black : TaoSection7Point → Prop) (r : ℝ)
    (family : Set TaoSection7Triangle) : Prop :=
  ∀ ⦃Δ : TaoSection7Triangle⦄, Δ ∈ family → Δ.ClaimStar black r

theorem TaoSection7TriangleFamilySeparatedBy.of_claimStar
    {black : TaoSection7Point → Prop} {r : ℝ} {family : Set TaoSection7Triangle}
    (hstar : TaoSection7TriangleFamilyClaimStar black r family)
    (hblack : TaoSection7TriangleFamilyBlackOn black family)
    (hdisj : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    TaoSection7TriangleFamilySeparatedBy r family := by
  intro Δ Γ hΔ hΓ hne
  exact TaoSection7Triangle.separatedBy_of_claimStar_and_disjoint
    (hstar hΔ) (hblack hΓ) (hdisj hΔ hΓ hne)

structure TaoSection7TopLeftWitness
    (black : TaoSection7Point → Prop) (p : TaoSection7Point) where
  topLeft : TaoSection7Point
  topLeft_j_le : topLeft.j ≤ p.j
  source_l_le_topLeft_l : p.l ≤ topLeft.l
  vertical_black :
    ∀ q : TaoSection7Point,
      q.j = p.j → p.l ≤ q.l → q.l ≤ topLeft.l → black q
  vertical_up_white :
    ¬ black ⟨p.j, topLeft.l + 1⟩
  horizontal_black :
    ∀ q : TaoSection7Point,
      topLeft.j ≤ q.j → q.j ≤ p.j → q.l = topLeft.l → black q
  left_boundary_white :
    (topLeft.j : ℕ) = 1 ∨
      ∃ h : 1 < (topLeft.j : ℕ), ¬ black (topLeft.left h)

namespace TaoSection7TopLeftWitness

def columnTop {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) : TaoSection7Point :=
  ⟨p.j, w.topLeft.l⟩

def columnTopUp {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) : TaoSection7Point :=
  ⟨p.j, w.topLeft.l + 1⟩

def triangle {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) (size : ℝ) : TaoSection7Triangle :=
  ⟨w.topLeft.j, w.topLeft.l, size⟩

theorem columnTop_black {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) :
    black w.columnTop := by
  exact w.vertical_black w.columnTop rfl w.source_l_le_topLeft_l le_rfl

theorem columnTopUp_white {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) :
    ¬ black w.columnTopUp :=
  w.vertical_up_white

theorem topLeft_black {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) :
    black w.topLeft := by
  exact w.horizontal_black w.topLeft le_rfl w.topLeft_j_le rfl

theorem triangle_topLeft
    {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) (size : ℝ) :
    (w.triangle size).topLeft = w.topLeft := by
  rfl

theorem triangle_topLeft_mem
    {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) {size : ℝ} (hsize : 0 ≤ size) :
    (w.triangle size).Mem w.topLeft := by
  simpa [triangle_topLeft] using
    TaoSection7Triangle.topLeft_mem_of_nonneg (Δ := w.triangle size) hsize

end TaoSection7TopLeftWitness

namespace TaoSection7TriangleSeed

end TaoSection7TriangleSeed

end

end Tao

end Erdos1135Predecessor
