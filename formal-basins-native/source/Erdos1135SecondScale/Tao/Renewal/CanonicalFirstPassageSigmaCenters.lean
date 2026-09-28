/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7Geometry
import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageSignedCenterSum

/-!
# Canonical First-Passage Bounds on Section 7 Centers

This leaf projects the separated point set `Sigma` to its common horizontal
integer row and feeds that image to the checked sparse-center kernel bound.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped BigOperators

namespace TaoSection7Lemma710

/-- Horizontal integer coordinate of a Section 7 lattice point. -/
def sigmaHorizontalCoord (p : TaoSection7Point) : ℤ :=
  ((p.j : ℕ) : ℤ)

/-- Separation scale supplied by the disjoint-triangle geometry. -/
def sigmaSeparationScale (sMin : ℝ) : ℝ :=
  (Real.log 2 / (4 * Real.log 9)) * sMin

/-- Horizontal integer image of the Lemma 7.10 center set. -/
def sigmaHorizontalCenters
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (sMin K B : ℝ) : Set ℤ :=
  sigmaHorizontalCoord '' Sigma family old sMin K B

theorem sigmaHorizontalCoord_injOn
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ} :
    Set.InjOn sigmaHorizontalCoord (Sigma family old sMin K B) := by
  intro p hp q hq hj
  have hj' : p.j = q.j := by
    apply Subtype.ext
    change ((p.j : ℕ) : ℤ) = ((q.j : ℕ) : ℤ) at hj
    exact Int.ofNat.inj hj
  have hl' : p.l = q.l := by
    rw [sigma_same_horizontal hp, sigma_same_horizontal hq]
  cases p
  cases q
  simp_all

/-- The center set is equivalent to its horizontal integer image. -/
def sigmaEquivHorizontalCenters
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ} :
    (Sigma family old sMin K B) ≃
      sigmaHorizontalCenters family old sMin K B :=
  Equiv.Set.imageOfInjOn sigmaHorizontalCoord _ sigmaHorizontalCoord_injOn

theorem tsum_sigma_eq_tsum_horizontalCenters
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (f : ℤ → ℝ) :
    (∑' p : Sigma family old sMin K B,
      f (sigmaHorizontalCoord p.1)) =
      ∑' z : sigmaHorizontalCenters family old sMin K B, f z.1 := by
  simpa using
    (sigmaEquivHorizontalCenters
      (family := family) (old := old) (sMin := sMin) (K := K) (B := B)).tsum_eq
        (fun z => f z.1)

theorem natFloor_sq_le_of_sq_le
    {D S : ℝ} (hD : 0 ≤ D) (hDS : D ^ 2 ≤ S) :
    (Nat.floor D : ℝ) ^ 2 ≤ S := by
  have hfloor : (Nat.floor D : ℝ) ≤ D := Nat.floor_le hD
  have hfloor_nonneg : (0 : ℝ) ≤ (Nat.floor D : ℝ) := Nat.cast_nonneg _
  exact (pow_le_pow_left₀ hfloor_nonneg hfloor 2).trans hDS

/-- Distinct horizontal images of `Sigma` retain the floor of the geometric
separation scale. -/
theorem sigmaHorizontalCenters_pairwise_floorSeparation
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin) :
    (sigmaHorizontalCenters family old sMin K B).Pairwise
      (fun z₁ z₂ =>
        (Nat.floor (sigmaSeparationScale sMin) : ℤ) ≤ |z₁ - z₂|) := by
  rintro z₁ ⟨p, hp, rfl⟩ z₂ ⟨q, hq, rfl⟩ hne
  have hpq : p ≠ q := by
    intro hpq
    apply hne
    simpa [hpq]
  have hscale_nonneg : 0 ≤ sigmaSeparationScale sMin := by
    exact separationScale_nonneg_of_gapAbsorbs habsorb
  have hdist :=
    sigma_distSq_ge_of_pairwiseDisjoint_autoRows hpair habsorb hp hq hpq
  have hdist' :
      (sigmaSeparationScale sMin) ^ 2 ≤
        ((((p.j : ℕ) : ℝ) - ((q.j : ℕ) : ℝ)) ^ 2) := by
    simpa [sigmaSeparationScale, TaoSection7Point.distSq,
      TaoSection7Point.jReal, TaoSection7Point.lReal,
      sigma_same_horizontal hp, sigma_same_horizontal hq] using hdist
  have hgap_real :
      sigmaSeparationScale sMin ≤
        |(((p.j : ℕ) : ℝ) - ((q.j : ℕ) : ℝ))| := by
    have habs_nonneg :
        0 ≤ |(((p.j : ℕ) : ℝ) - ((q.j : ℕ) : ℝ))| := abs_nonneg _
    have habs_sq :
        |(((p.j : ℕ) : ℝ) - ((q.j : ℕ) : ℝ))| ^ 2 =
          (((p.j : ℕ) : ℝ) - ((q.j : ℕ) : ℝ)) ^ 2 := sq_abs _
    nlinarith
  have hfloor_real :
      (Nat.floor (sigmaSeparationScale sMin) : ℝ) ≤
        |(((p.j : ℕ) : ℝ) - ((q.j : ℕ) : ℝ))| :=
    (Nat.floor_le hscale_nonneg).trans hgap_real
  have hfloor_cast :
      (((Nat.floor (sigmaSeparationScale sMin) : ℤ) : ℝ)) ≤
        ((|sigmaHorizontalCoord p - sigmaHorizontalCoord q| : ℤ) : ℝ) := by
    simpa [sigmaHorizontalCoord] using hfloor_real
  exact_mod_cast hfloor_cast

/-- The checked sparse-center kernel estimate specialized to the horizontal
image of the geometric center set `Sigma`. -/
theorem lemma77SignedTranslatedHorizontalKernel_tsum_sigma_le
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {sMin K B : ℝ}
    {C c : ℝ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (habsorb : TaoSection7Triangle.lemma710GapAbsorbs K B sMin)
    (hC : 0 ≤ C) (hc : 0 < c)
    (shift : ℤ) (s : ℕ)
    (hscale : 1 ≤ sigmaSeparationScale sMin)
    (hwidth : (sigmaSeparationScale sMin) ^ 2 ≤ 1 + (s : ℝ)) :
    (∑' p : Sigma family old sMin K B,
      TaoSection7Lemma77.lemma77SignedTranslatedHorizontalKernel
        C (c / 2) shift s (sigmaHorizontalCoord p.1)) ≤
      (2 * Real.exp ((c / 2) ^ 2) /
          (Nat.floor (sigmaSeparationScale sMin) : ℝ)) *
        (C *
          (TaoSection7Lemma77.lemma77HorizontalGaussianCountConstant
              ((c / 4) ^ 2) +
            TaoSection7Lemma77.lemma77HorizontalLinearCountConstant (c / 4))) := by
  rw [tsum_sigma_eq_tsum_horizontalCenters]
  apply
    TaoSection7Lemma77.lemma77SignedTranslatedHorizontalKernel_tsum_separated_centers_le
      hC hc shift s (Nat.floor (sigmaSeparationScale sMin))
  · exact Nat.floor_pos.mpr hscale
  · exact natFloor_sq_le_of_sq_le
      (le_trans (by norm_num) hscale) hwidth
  · exact sigmaHorizontalCenters_pairwise_floorSeparation hpair habsorb

end TaoSection7Lemma710

end
end Tao
end Erdos1135SecondScale
