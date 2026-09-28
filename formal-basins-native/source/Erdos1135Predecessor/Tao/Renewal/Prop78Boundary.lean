/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.GeometryBridge
import Erdos1135Predecessor.Tao.Renewal.QmStatement

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection7QmBoundary_toPoint_sourceDomain
    {J m : ℕ} {p : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary J m p) :
    taoSection7SourcePointInDomain J p.toPoint := by
  unfold taoSection7SourcePointInDomain taoSection7QmBoundary at *
  simp [TaoSection7RenewalPoint.toPoint]
  omega

noncomputable def taoSection7Prop78BoundaryThreshold (m : ℕ) : ℝ :=
  (m : ℝ) / (Real.log (m : ℝ)) ^ 2

noncomputable def taoSection7Prop78NearTop
    (m : ℕ) (Δ : TaoSection7Triangle) (p : TaoSection7Point) : Prop :=
  ((Δ.verticalDepth p : ℤ) : ℝ) ≤ taoSection7Prop78BoundaryThreshold m

noncomputable def taoSection7Prop78FarBelowTop
    (m : ℕ) (Δ : TaoSection7Triangle) (p : TaoSection7Point) : Prop :=
  taoSection7Prop78BoundaryThreshold m < ((Δ.verticalDepth p : ℤ) : ℝ)

theorem taoSection7Prop78NearTop_or_FarBelowTop
    (m : ℕ) (Δ : TaoSection7Triangle) (p : TaoSection7Point) :
    taoSection7Prop78NearTop m Δ p ∨
      taoSection7Prop78FarBelowTop m Δ p := by
  unfold taoSection7Prop78NearTop taoSection7Prop78FarBelowTop
  exact le_or_gt _ _

noncomputable def TaoSection7QmBoundaryNearTop
    (threshold : ℝ) (family : Set TaoSection7Triangle)
    (p : TaoSection7RenewalPoint) : Prop :=
  ∃ Δ ∈ family, Δ.Mem p.toPoint ∧
    ((Δ.verticalDepth p.toPoint : ℤ) : ℝ) ≤ threshold

noncomputable def TaoSection7QmBoundaryFarBelow
    (threshold : ℝ) (family : Set TaoSection7Triangle)
    (p : TaoSection7RenewalPoint) : Prop :=
  ∃ Δ ∈ family, Δ.Mem p.toPoint ∧
    threshold < ((Δ.verticalDepth p.toPoint : ℤ) : ℝ)

theorem taoSection7SourceTriangleCover_renewalPoint_of_qmBoundary_not_cutoffWhite
    {n J m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    {p : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary J m p)
    (hnotWhite : ¬ taoSection7SourceWhiteRenewal
      (taoSection7SourceWhiteWCutoff n xi epsilon J) p) :
    ∃ Δ ∈ family, Δ.Mem p.toPoint :=
  taoSection7SourceTriangleCover_renewalPoint_of_not_cutoffWhite hcover
    (taoSection7QmBoundary_toPoint_sourceDomain hboundary) hnotWhite

theorem taoSection7QmBoundary_partition_of_source_triangle_cover_concrete
    {n J m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    {p : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary J m p) :
    taoSection7SourceWhiteRenewal
        (taoSection7SourceWhiteWCutoff n xi epsilon J) p ∨
      TaoSection7QmBoundaryNearTop
        (taoSection7Prop78BoundaryThreshold m) family p ∨
        TaoSection7QmBoundaryFarBelow
          (taoSection7Prop78BoundaryThreshold m) family p := by
  classical
  by_cases hwhite :
      taoSection7SourceWhiteRenewal
        (taoSection7SourceWhiteWCutoff n xi epsilon J) p
  · exact Or.inl hwhite
  · right
    rcases taoSection7SourceTriangleCover_renewalPoint_of_qmBoundary_not_cutoffWhite
        hcover hboundary hwhite with ⟨Δ, hΔ, hpΔ⟩
    rcases taoSection7Prop78NearTop_or_FarBelowTop m Δ p.toPoint with hnear | hfar
    · left
      exact ⟨Δ, hΔ, hpΔ, hnear⟩
    · right
      exact ⟨Δ, hΔ, hpΔ, hfar⟩

theorem taoSection7QmBoundaryAtCutoff_partition_of_source_triangle_cover_concrete
    {n m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family)
    {p : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m p) :
    taoSection7SourceActualW n xi epsilon p ∨
      TaoSection7QmBoundaryNearTop
        (taoSection7Prop78BoundaryThreshold m) family p ∨
        TaoSection7QmBoundaryFarBelow
          (taoSection7Prop78BoundaryThreshold m) family p := by
  simpa [taoSection7SourceActualW] using
    (taoSection7QmBoundary_partition_of_source_triangle_cover_concrete
    (n := n) (J := n / 2) (m := m) (xi := xi) (epsilon := epsilon)
    (family := family) hcover hboundary)

end Tao

end Erdos1135Predecessor
