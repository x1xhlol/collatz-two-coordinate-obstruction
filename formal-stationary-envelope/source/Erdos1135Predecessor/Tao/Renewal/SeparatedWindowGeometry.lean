/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.SeparatedWindowSum

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

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

theorem abs_sub_center_le_of_mem_taoSection7CenteredHalfOpenIntWindow
    {d : ℕ} {center z : ℤ}
    (hz : z ∈ taoSection7CenteredHalfOpenIntWindow d center) :
    |center - z| ≤ (d : ℤ) := by
  simp only [taoSection7CenteredHalfOpenIntWindow, Finset.mem_Ico] at hz
  have hhalf : ((d / 2 : ℕ) : ℤ) ≤ (d : ℤ) := by
    exact_mod_cast Nat.div_le_self d 2
  rw [abs_le]
  constructor <;> omega

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

end

end Tao

end Erdos1135Predecessor
