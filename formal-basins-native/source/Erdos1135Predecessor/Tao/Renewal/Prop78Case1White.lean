/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case1Scalar
import Erdos1135Predecessor.Tao.Renewal.QmStatement

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection7QmBoundary_add_hold_tail_prev
    {J m : ℕ} {p h : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary J m p) :
    taoSection7QmTail J (m - 1) (p + h) := by
  unfold taoSection7QmBoundary taoSection7QmTail at *
  simp only [TaoSection7RenewalPoint.add_j, PNat.add_coe] at *
  have hh : 1 ≤ (h.j : ℕ) := h.j.2
  omega

theorem taoSection7QDistanceToCutoff_add_hold_of_boundary
    {J m : ℕ} {p h : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary J m p) :
    taoSection7QDistanceToCutoff J (p + h) =
      max (m - (h.j : ℕ)) 1 := by
  unfold taoSection7QDistanceToCutoff taoSection7QmBoundary at *
  simp only [TaoSection7RenewalPoint.add_j, PNat.add_coe] at *
  congr 1
  omega

theorem taoSection7QmWeightedValue_le_sourceQm
    {J A k : ℕ} {Q : TaoSection7Q} {p : TaoSection7RenewalPoint}
    (hbdd : BddAbove (taoSection7QmValueSet J A Q k))
    (hp : taoSection7QmTail J k p) :
    taoSection7QmWeightedValue J A Q p ≤
      taoSection7SourceQm J A Q k := by
  unfold taoSection7SourceQm
  exact le_csSup hbdd ⟨p, hp, rfl⟩

theorem taoSection7Case1InvPow_nonneg (A m : ℕ) (r : ℕ+) :
    0 ≤ taoSection7Case1InvPow A m r := by
  unfold taoSection7Case1InvPow
  positivity

theorem taoSection7Case1InvPow_le_one (A m : ℕ) (r : ℕ+) :
    taoSection7Case1InvPow A m r ≤ 1 := by
  unfold taoSection7Case1InvPow
  apply pow_le_one₀ (by positivity)
  exact inv_le_one_of_one_le₀ (by
    exact_mod_cast (le_max_right (m - (r : ℕ)) 1))

theorem taoSection7SourceActualQ_add_hold_le_case1InvPow_mul_qmPrev
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary (n / 2) m p)
    (h : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon (p + h) ≤
      taoSection7Case1InvPow A m h.j *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  have htail := taoSection7QmBoundary_add_hold_tail_prev hp (h := h)
  have hbdd := taoSection7QmValueSet_bddAbove_of_bounded01
    (J := n / 2) (A := A) (m := m - 1)
    (Q := taoSection7SourceActualQ n xi epsilon)
    (taoSection7SourceActualQ_bounded01
      (n := n) (xi := xi) hepsilon)
  have hw := taoSection7QmWeightedValue_le_sourceQm
    (J := n / 2) (A := A) (k := m - 1)
    (Q := taoSection7SourceActualQ n xi epsilon)
    hbdd htail
  unfold taoSection7QmWeightedValue at hw
  rw [taoSection7QDistanceToCutoff_add_hold_of_boundary hp] at hw
  have hw' :
      ((max (m - (h.j : ℕ)) 1 : ℕ) : ℝ) ^ A *
          taoSection7SourceActualQ n xi epsilon (p + h) ≤
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
    simpa [taoSection7SourceActualQmAtCutoff,
      taoSection7SourceActualQm] using hw
  let d : ℕ := max (m - (h.j : ℕ)) 1
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
  have hdne : (d : ℝ) ^ A ≠ 0 := ne_of_gt (pow_pos hd A)
  have hwd :
      (d : ℝ) ^ A * taoSection7SourceActualQ n xi epsilon (p + h) ≤
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
    simpa [d] using hw'
  change taoSection7SourceActualQ n xi epsilon (p + h) ≤
    (((d : ℝ)⁻¹) ^ A) *
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon
  calc
    taoSection7SourceActualQ n xi epsilon (p + h) =
        (((d : ℝ) ^ A)⁻¹) *
          ((d : ℝ) ^ A * taoSection7SourceActualQ n xi epsilon (p + h)) := by
      field_simp [hdne]
    _ ≤ (((d : ℝ) ^ A)⁻¹) *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
      exact mul_le_mul_of_nonneg_left hwd (by positivity)
    _ = (((d : ℝ)⁻¹) ^ A) *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
      rw [inv_pow]

theorem taoSection7HoldExpectationFull_case1InvPow_j_eq
    (A m : ℕ) :
    taoSection7HoldExpectationFull
        (fun h => taoSection7Case1InvPow A m h.j) =
      taoSection7Case1InvPowMoment A m := by
  have htransport := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    taoSection7HoldPMF (fun h : TaoSection7RenewalPoint => h.j)
    (taoSection7Case1InvPow A m)
    (taoSection7Case1InvPow_nonneg A m)
    (taoSection7Case1InvPow_le_one A m)
  have hmap := taoSection7HoldPMF_map_j_eq_geom4PNat_checked
  unfold taoSection7HoldPMF_map_j_eq_geom4PNat at hmap
  rw [hmap] at htransport
  unfold taoSection7HoldExpectationFull taoSection7Case1InvPowMoment
  exact htransport.2.2.symm

theorem taoSection7HoldExpectationFull_shiftedActualQ_le_case1Moment_mul_qmPrev
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary (n / 2) m p) :
    taoSection7HoldExpectationFull
        (fun h => taoSection7SourceActualQ n xi epsilon (p + h)) ≤
      taoSection7Case1InvPowMoment A m *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  let B := taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon
  have hQ := taoSection7SourceActualQ_bounded01
    (n := n) (xi := xi) hepsilon
  have hsLeft : Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal *
        taoSection7SourceActualQ n xi epsilon (p + h) :=
    taoSection7HoldExpectationFull_summable_of_bounded01
      (fun h => (hQ (p + h)).1) (fun h => (hQ (p + h)).2)
  have htransport := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    taoSection7HoldPMF (fun h : TaoSection7RenewalPoint => h.j)
    (taoSection7Case1InvPow A m)
    (taoSection7Case1InvPow_nonneg A m)
    (taoSection7Case1InvPow_le_one A m)
  have hsInv : Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal * taoSection7Case1InvPow A m h.j :=
    htransport.2.1
  have hsRight : Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal *
        (taoSection7Case1InvPow A m h.j * B) := by
    exact (hsInv.mul_right B).congr (fun h => by ring)
  have hpoint : ∀ h : TaoSection7RenewalPoint,
      (taoSection7HoldPMF h).toReal *
          taoSection7SourceActualQ n xi epsilon (p + h) ≤
        (taoSection7HoldPMF h).toReal *
          (taoSection7Case1InvPow A m h.j * B) := by
    intro h
    exact mul_le_mul_of_nonneg_left
      (taoSection7SourceActualQ_add_hold_le_case1InvPow_mul_qmPrev
        hepsilon hp h) ENNReal.toReal_nonneg
  unfold taoSection7HoldExpectationFull
  calc
    (∑' h : TaoSection7RenewalPoint,
      (taoSection7HoldPMF h).toReal *
        taoSection7SourceActualQ n xi epsilon (p + h)) ≤
        ∑' h : TaoSection7RenewalPoint,
          (taoSection7HoldPMF h).toReal *
            (taoSection7Case1InvPow A m h.j * B) :=
      hsLeft.tsum_le_tsum hpoint hsRight
    _ = (∑' h : TaoSection7RenewalPoint,
        (taoSection7HoldPMF h).toReal *
          taoSection7Case1InvPow A m h.j) * B := by
      calc
        _ = ∑' h : TaoSection7RenewalPoint,
            ((taoSection7HoldPMF h).toReal *
              taoSection7Case1InvPow A m h.j) * B := by
          apply tsum_congr
          intro h
          ring
        _ = _ := tsum_mul_right
    _ = taoSection7Case1InvPowMoment A m * B := by
      have hid := taoSection7HoldExpectationFull_case1InvPow_j_eq A m
      unfold taoSection7HoldExpectationFull at hid
      rw [hid]

theorem taoSection7Prop78_case1_cutoffWhite_of_halfContraction
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (_hm : 2 ≤ m)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary (n / 2) m p)
    (hwhite : taoSection7SourceActualW n xi epsilon p)
    (hcontract :
      Real.exp (-(epsilon ^ 3)) * taoSection7Case1InvPowMoment A m ≤
        Real.exp (-(epsilon ^ 3 / 2)) * ((m : ℝ)⁻¹ ^ A)) :
    taoSection7SourceActualQ n xi epsilon p ≤
      Real.exp (-(epsilon ^ 3 / 2)) * ((m : ℝ) ^ A)⁻¹ *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  have hB : 0 ≤ taoSection7SourceActualQmAtCutoff
      n A (m - 1) xi epsilon :=
    taoSection7SourceActualQmAtCutoff_nonneg hepsilon
  rw [taoSection7SourceActualQ_fullHoldQRecursion hepsilon p]
  unfold taoSection7FullHoldQRecursionRHS
  rw [show taoSection7QWhiteFactor epsilon
      (taoSection7SourceActualW n xi epsilon) p =
        Real.exp (-(epsilon ^ 3)) by
    simp [taoSection7QWhiteFactor, hwhite]]
  calc
    Real.exp (-(epsilon ^ 3)) *
        taoSection7HoldExpectationFull
          (fun h => taoSection7SourceActualQ n xi epsilon (p + h)) ≤
      Real.exp (-(epsilon ^ 3)) *
        (taoSection7Case1InvPowMoment A m *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) := by
      gcongr
      exact taoSection7HoldExpectationFull_shiftedActualQ_le_case1Moment_mul_qmPrev
        hepsilon hp
    _ = (Real.exp (-(epsilon ^ 3)) *
        taoSection7Case1InvPowMoment A m) *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by ring
    _ ≤ (Real.exp (-(epsilon ^ 3 / 2)) * ((m : ℝ)⁻¹ ^ A)) *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon :=
      mul_le_mul_of_nonneg_right hcontract hB
    _ = Real.exp (-(epsilon ^ 3 / 2)) * ((m : ℝ) ^ A)⁻¹ *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
      rw [inv_pow]

end Tao

end Erdos1135Predecessor
