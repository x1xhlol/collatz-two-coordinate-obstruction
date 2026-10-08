/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QmStatement

namespace Erdos1135Predecessor

namespace Tao

structure TaoSection7Prop78Threshold
    (A : ℕ) (epsilon : ℝ) (C : ℕ) : Prop where
  lowerThreshold_le : taoSection7Prop78LowerThreshold ≤ C

theorem taoSection7Prop78LowerThreshold_le_of_threshold
    {A C : ℕ} {epsilon : ℝ}
    (hC : TaoSection7Prop78Threshold A epsilon C) :
    taoSection7Prop78LowerThreshold ≤ C :=
  hC.lowerThreshold_le

theorem taoSection7Prop78Threshold_to_lowerThreshold
    {A C m : ℕ} {epsilon : ℝ}
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m) :
    taoSection7Prop78LowerThreshold ≤ m :=
  le_trans (taoSection7Prop78LowerThreshold_le_of_threshold hC) hm_low

theorem taoSection7Prop78_boundary741
    {n A C m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m)
    (hm_hi : m ≤ n / 2)
    (hboundary741 : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  have _hm_local : taoSection7Prop78LowerThreshold ≤ m :=
    taoSection7Prop78Threshold_to_lowerThreshold hC hm_low
  have _hm_hi : m ≤ n / 2 := hm_hi
  intro p hp
  exact hboundary741 p hp

theorem taoSection7_prop78_monotonicity_740
    {n A C m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m)
    (hm_hi : m ≤ n / 2)
    (hboundary741 : ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  exact taoSection7SourceProp78Monotonicity
    (n := n) (A := A) (m := m) (xi := xi) (epsilon := epsilon)
    hepsilon
    (taoSection7Prop78Threshold_to_lowerThreshold hC hm_low)
    hm_hi
    (taoSection7Prop78_boundary741
      (n := n) (A := A) (C := C) (m := m)
      (xi := xi) (epsilon := epsilon)
      hC hm_low hm_hi hboundary741)

end Tao

end Erdos1135Predecessor
