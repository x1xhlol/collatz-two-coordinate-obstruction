import Erdos1135.Tao.Fourier.Section7SourceDomain
import Erdos1135.Tao.Renewal.SourceListBridge

/-!
# Section 7 Renewal/Geometry Bridge

This module transports renewal points to Section 7 source-geometry points and
records cutoff/domain bridges needed before Proposition 7.8 boundary cases.
It does not prove Lemma 7.4, the boundary estimate `(7.41)`, Proposition 7.8,
or any decay estimate.
-/

namespace Erdos1135
namespace Tao

namespace TaoSection7RenewalPoint

/-- Regard a renewal point as a Section 7 lattice point. -/
def toPoint (p : TaoSection7RenewalPoint) : TaoSection7Point :=
  { j := p.j, l := p.l }

@[simp] theorem toPoint_j (p : TaoSection7RenewalPoint) :
    (p.toPoint.j : ℕ) = (p.j : ℕ) :=
  rfl

@[simp] theorem toPoint_l (p : TaoSection7RenewalPoint) :
    p.toPoint.l = p.l :=
  rfl

@[simp] theorem toPoint_mk (j : ℕ+) (l : ℤ) :
    ({ j := j, l := l } : TaoSection7RenewalPoint).toPoint =
      ({ j := j, l := l } : TaoSection7Point) :=
  rfl

theorem toPoint_injective :
    Function.Injective TaoSection7RenewalPoint.toPoint := by
  intro p q hpq
  ext
  · exact congrArg (fun r : TaoSection7Point => r.j) hpq
  · exact congrArg (fun r : TaoSection7Point => r.l) hpq

end TaoSection7RenewalPoint

/-- Source-domain membership transported to renewal points. -/
def taoSection7RenewalPointInSourceDomain
    (J : ℕ) (p : TaoSection7RenewalPoint) : Prop :=
  taoSection7SourcePointInDomain J p.toPoint

theorem taoSection7RenewalPointInSourceDomain_iff
    {J : ℕ} {p : TaoSection7RenewalPoint} :
    taoSection7RenewalPointInSourceDomain J p ↔ (p.j : ℕ) ≤ J := by
  rfl

theorem taoSection7SourceWhiteRenewal_cutoff_iff_toPoint
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7RenewalPoint} :
    taoSection7SourceWhiteRenewal
        (taoSection7SourceWhiteWCutoff n xi epsilon J) p ↔
      taoSection7SourcePointInDomain J p.toPoint ∧
        taoSection7SourceWhitePoint n xi epsilon p.toPoint := by
  constructor
  · intro h
    rcases h with ⟨_hj, hJ, hwhite⟩
    exact ⟨hJ, by simpa [TaoSection7RenewalPoint.toPoint] using hwhite⟩
  · rintro ⟨hJ, hwhite⟩
    exact ⟨p.j.property, hJ,
      by simpa [TaoSection7RenewalPoint.toPoint] using hwhite⟩

theorem taoSection7SourceWhiteRenewal_cutoff_domain
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7RenewalPoint}
    (hwhite : taoSection7SourceWhiteRenewal
      (taoSection7SourceWhiteWCutoff n xi epsilon J) p) :
    taoSection7SourcePointInDomain J p.toPoint :=
  (taoSection7SourceWhiteRenewal_cutoff_iff_toPoint.mp hwhite).1

theorem taoSection7SourceWhiteRenewal_cutoff_rawPoint
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7RenewalPoint}
    (hwhite : taoSection7SourceWhiteRenewal
      (taoSection7SourceWhiteWCutoff n xi epsilon J) p) :
    taoSection7SourceWhitePoint n xi epsilon p.toPoint :=
  (taoSection7SourceWhiteRenewal_cutoff_iff_toPoint.mp hwhite).2

theorem taoSection7SourceWhitePoint_iff_not_blackPoint
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point} :
    taoSection7SourceWhitePoint n xi epsilon p ↔
      ¬ taoSection7SourceBlackPoint n xi epsilon p := by
  simpa [taoSection7SourceWhitePoint, taoSection7SourceBlackPoint] using
    (taoSection7White_iff_not_black
      (epsilon := epsilon) (z := taoSection7ThetaResidue n xi p.j p.l))

theorem taoSection7SourceBlackInDomain_toPoint_of_not_cutoffWhite
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7RenewalPoint}
    (hdomain : taoSection7SourcePointInDomain J p.toPoint)
    (hnotWhite : ¬ taoSection7SourceWhiteRenewal
      (taoSection7SourceWhiteWCutoff n xi epsilon J) p) :
    taoSection7SourceBlackInDomain n xi epsilon J p.toPoint := by
  refine ⟨hdomain, ?_⟩
  classical
  by_contra hblack
  have hwhitePoint : taoSection7SourceWhitePoint n xi epsilon p.toPoint :=
    (taoSection7SourceWhitePoint_iff_not_blackPoint).2 hblack
  exact hnotWhite
    (taoSection7SourceWhiteRenewal_cutoff_iff_toPoint.mpr
      ⟨hdomain, hwhitePoint⟩)

theorem taoSection7TriangleFamilyCoverBlack_renewalPoint
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    {p : TaoSection7RenewalPoint}
    (hblack : taoSection7SourceBlackInDomain n xi epsilon J p.toPoint) :
    ∃ Δ ∈ family, Δ.Mem p.toPoint :=
  (hcover p.toPoint).mp hblack

theorem taoSection7SourceTriangleCover_renewalPoint_of_not_cutoffWhite
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon J) family)
    {p : TaoSection7RenewalPoint}
    (hdomain : taoSection7SourcePointInDomain J p.toPoint)
    (hnotWhite : ¬ taoSection7SourceWhiteRenewal
      (taoSection7SourceWhiteWCutoff n xi epsilon J) p) :
    ∃ Δ ∈ family, Δ.Mem p.toPoint :=
  taoSection7TriangleFamilyCoverBlack_renewalPoint hcover
    (taoSection7SourceBlackInDomain_toPoint_of_not_cutoffWhite
      hdomain hnotWhite)

end Tao
end Erdos1135
