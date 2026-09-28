/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.SeparatedWindowSum

/-!
# Exact Integer Window Geometry

This neutral leaf supplies exact-cardinality half-open integer windows and the
spacing-to-disjointness facts used by the signed sparse-kernel argument.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

noncomputable section

/-- Centered half-open integer window of exact cardinality `d`. -/
def taoSection7CenteredHalfOpenIntWindow (d : ℕ) (center : ℤ) : Finset ℤ :=
  let lower := center - ((d / 2 : ℕ) : ℤ)
  Finset.Ico lower (lower + (d : ℤ))

@[simp] theorem card_taoSection7CenteredHalfOpenIntWindow
    (d : ℕ) (center : ℤ) :
    (taoSection7CenteredHalfOpenIntWindow d center).card = d := by
  unfold taoSection7CenteredHalfOpenIntWindow
  rw [Int.card_Ico]
  have hdiff :
      center - ((d / 2 : ℕ) : ℤ) + (d : ℤ) -
          (center - ((d / 2 : ℕ) : ℤ)) = (d : ℤ) := by
    ring
  rw [hdiff, Int.toNat_natCast]

/-- Every point of the centered window lies within its full width of the
center. -/
theorem abs_sub_center_le_of_mem_taoSection7CenteredHalfOpenIntWindow
    {d : ℕ} {center z : ℤ}
    (hz : z ∈ taoSection7CenteredHalfOpenIntWindow d center) :
    |center - z| ≤ (d : ℤ) := by
  simp only [taoSection7CenteredHalfOpenIntWindow, Finset.mem_Ico] at hz
  have hhalf : ((d / 2 : ℕ) : ℤ) ≤ (d : ℤ) := by
    exact_mod_cast Nat.div_le_self d 2
  rw [abs_le]
  constructor <;> omega

/-- Exact membership transport under integer translation. -/
theorem add_mem_taoSection7CenteredHalfOpenIntWindow_add
    (d : ℕ) (center shift z : ℤ) :
    z + shift ∈ taoSection7CenteredHalfOpenIntWindow d (center + shift) ↔
      z ∈ taoSection7CenteredHalfOpenIntWindow d center := by
  simp only [taoSection7CenteredHalfOpenIntWindow, Finset.mem_Ico]
  constructor <;> omega

/-- Equality in the center-gap lower bound is enough for disjointness because
the windows are half-open. -/
theorem taoSection7CenteredHalfOpenIntWindow_disjoint_of_width_le_abs_sub
    {d : ℕ} {c₁ c₂ : ℤ}
    (hsep : (d : ℤ) ≤ |c₁ - c₂|) :
    Disjoint (taoSection7CenteredHalfOpenIntWindow d c₁)
      (taoSection7CenteredHalfOpenIntWindow d c₂) := by
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  simp only [taoSection7CenteredHalfOpenIntWindow, Finset.mem_Ico] at hz₁ hz₂
  rcases le_total c₁ c₂ with h₁₂ | h₂₁
  · rw [abs_of_nonpos (sub_nonpos.mpr h₁₂)] at hsep
    omega
  · rw [abs_of_nonneg (sub_nonneg.mpr h₂₁)] at hsep
    omega

/-- Pairwise `d`-separated centers have pairwise disjoint exact-length
windows. -/
theorem taoSection7CenteredHalfOpenIntWindow_pairwiseDisjoint
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (center : ι → ℤ) (d : ℕ)
    (hsep : (S : Set ι).Pairwise
      (fun i j => (d : ℤ) ≤ |center i - center j|)) :
    Set.PairwiseDisjoint (S : Set ι)
      (fun i => taoSection7CenteredHalfOpenIntWindow d (center i)) := by
  intro i hi j hj hij
  exact taoSection7CenteredHalfOpenIntWindow_disjoint_of_width_le_abs_sub
    (hsep hi hj hij)

end
end Tao
end Erdos1135SecondScale
