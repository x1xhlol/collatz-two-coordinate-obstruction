import Erdos1135.Tao.Renewal.Prop78Boundary
import Erdos1135.Tao.Renewal.Prop78Threshold

/-!
# Section 7 Proposition 7.8 Case Assembly Socket

This module records the checked join point from Tao's three boundary cases to
the exact supplied `(7.41)` hypothesis consumed by the source `Q_m`
monotonicity wrapper.  It does not prove any of the three case estimates,
the boundary estimate `(7.41)`, Proposition 7.8, Proposition 7.3, Proposition
7.1, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

/--
Three supplied case bounds for a `Q_m` boundary slice at the source cutoff.

The fields correspond to the cutoff-white branch, the near-top triangle
branch, and the far-below triangle branch from
`taoSection7QmBoundaryAtCutoff_partition_of_source_triangle_cover_concrete`.
Each field must prove the same pointwise `(7.41)` bound for the current
boundary point; this structure only packages those future case estimates.
-/
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

/--
Assemble the exact pointwise `(7.41)` boundary hypothesis from the checked
cutoff/near-top/far-below partition and supplied estimates for the three
branches.
-/
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

/--
Source-range monotonicity `(7.40)` from the three-case Prop. 7.8 boundary
socket.  The analytic case estimates remain hypotheses through
`TaoSection7Prop78BoundaryCaseBounds`.
-/
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
end Erdos1135
