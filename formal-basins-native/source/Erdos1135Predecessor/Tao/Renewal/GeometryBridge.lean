/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceDomain
import Erdos1135Predecessor.Tao.Renewal.SourceListBridge

namespace Erdos1135Predecessor

namespace Tao

namespace TaoSection7RenewalPoint

def toPoint (p : TaoSection7RenewalPoint) : TaoSection7Point :=
  { j := p.j, l := p.l }

@[simp] theorem toPoint_j (p : TaoSection7RenewalPoint) :
    (p.toPoint.j : ℕ) = (p.j : ℕ) :=
  rfl

@[simp] theorem toPoint_l (p : TaoSection7RenewalPoint) :
    p.toPoint.l = p.l :=
  rfl

theorem toPoint_injective :
    Function.Injective TaoSection7RenewalPoint.toPoint := by
  intro p q hpq
  ext
  · exact congrArg (fun r : TaoSection7Point => r.j) hpq
  · exact congrArg (fun r : TaoSection7Point => r.l) hpq

end TaoSection7RenewalPoint

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

end Erdos1135Predecessor
