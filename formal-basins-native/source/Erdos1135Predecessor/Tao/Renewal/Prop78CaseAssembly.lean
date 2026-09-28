/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Boundary
import Erdos1135Predecessor.Tao.Renewal.Prop78Threshold

namespace Erdos1135Predecessor

namespace Tao

structure TaoSection7Prop78BoundaryCaseBounds
    (n A m : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle) : Prop where
  cutoffWhite :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualW n xi epsilon p →
          taoSection7SourceActualQ n xi epsilon p ≤
            ((m : ℝ) ^ A)⁻¹ *
              taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon
  nearTop :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        TaoSection7QmBoundaryNearTop
          (taoSection7Prop78BoundaryThreshold m) family p →
          taoSection7SourceActualQ n xi epsilon p ≤
            ((m : ℝ) ^ A)⁻¹ *
              taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon
  farBelow :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        TaoSection7QmBoundaryFarBelow
          (taoSection7Prop78BoundaryThreshold m) family p →
          taoSection7SourceActualQ n xi epsilon p ≤
            ((m : ℝ) ^ A)⁻¹ *
              taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon

theorem taoSection7Prop78_boundary741_of_caseBounds
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family)
    (hcases :
      TaoSection7Prop78BoundaryCaseBounds n A m xi epsilon family) :
    ∀ p : TaoSection7RenewalPoint,
      taoSection7QmBoundary (n / 2) m p →
        taoSection7SourceActualQ n xi epsilon p ≤
          ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  intro p hp
  rcases taoSection7QmBoundaryAtCutoff_partition_of_source_triangle_cover_concrete
      (n := n) (m := m) (xi := xi) (epsilon := epsilon)
      (family := family) hcover hp with hwhite | hsplit
  · exact hcases.cutoffWhite p hp hwhite
  · rcases hsplit with hnear | hfar
    · exact hcases.nearTop p hp hnear
    · exact hcases.farBelow p hp hfar

theorem taoSection7_prop78_monotonicity_740_of_caseBounds
    {n A C m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hepsilon : 0 ≤ epsilon)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hm_low : C ≤ m)
    (hm_hi : m ≤ n / 2)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family)
    (hcases :
      TaoSection7Prop78BoundaryCaseBounds n A m xi epsilon family) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon := by
  exact taoSection7_prop78_monotonicity_740
    (n := n) (A := A) (C := C) (m := m) (xi := xi)
    (epsilon := epsilon) hepsilon hC hm_low hm_hi
    (taoSection7Prop78_boundary741_of_caseBounds
      (n := n) (A := A) (m := m) (xi := xi) (epsilon := epsilon)
      (family := family) hcover hcases)

end Tao

end Erdos1135Predecessor
