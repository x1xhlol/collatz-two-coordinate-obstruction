/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7Cancellation
import Erdos1135Predecessor.Tao.Renewal.SourceListBridge
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

def taoSection7SourceWhiteW
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    ℕ → ℤ → Prop :=
  fun j l =>
    ∃ hj : 0 < j,
      taoSection7White epsilon
        (taoSection7ThetaResidue n xi ⟨j, hj⟩ l)

theorem norm_taoForwardDFTKernel_eq_one
    {N : ℕ} [NeZero N] (x xi : ZMod N) :
    ‖taoForwardDFTKernel x xi‖ = 1 := by
  simp [taoForwardDFTKernel, ZMod.stdAddChar]

theorem norm_taoSection7PairAverage_le_one
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    ‖taoSection7PairAverage n xi x‖ ≤ 1 := by
  unfold taoSection7PairAverage
  calc
    ‖(1 / 2 : ℂ) * taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) xi +
        (1 / 2 : ℂ) * taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) xi‖
        ≤ ‖(1 / 2 : ℂ) * taoForwardDFTKernel ((5 : ZMod (3 ^ n)) * x) xi‖ +
            ‖(1 / 2 : ℂ) * taoForwardDFTKernel ((7 : ZMod (3 ^ n)) * x) xi‖ := by
          exact norm_add_le _ _
    _ = 1 := by
          rw [norm_mul, norm_mul]
          rw [norm_taoForwardDFTKernel_eq_one, norm_taoForwardDFTKernel_eq_one]
          norm_num

theorem norm_taoSection7FThree_le_one
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    ‖taoSection7FThree n xi x‖ ≤ 1 := by
  rw [norm_taoSection7FThree_eq_pairAverage]
  exact norm_taoSection7PairAverage_le_one n xi x

noncomputable def taoSection7SourceFThreeFactor
    (n : ℕ) (xi : ZMod (3 ^ n)) :
    ℕ → ℕ → ℕ → ℝ :=
  fun j s b =>
    if h : b = 3 ∧ 0 < j then
      ‖taoSection7FThree n xi
          (taoSection7PairX n ⟨j, h.2⟩ (Int.ofNat (s + b)))‖
    else
      1

theorem taoSection7SourceFThreeFactor_nonneg
    (n : ℕ) (xi : ZMod (3 ^ n)) :
    ∀ j s b, 0 ≤ taoSection7SourceFThreeFactor n xi j s b := by
  intro j s b
  unfold taoSection7SourceFThreeFactor
  split
  · exact norm_nonneg _
  · norm_num

theorem taoSection7SourceFThreeFactor_le_one
    (n : ℕ) (xi : ZMod (3 ^ n)) :
    ∀ j s b, taoSection7SourceFThreeFactor n xi j s b ≤ 1 := by
  intro j s b
  by_cases h : b = 3 ∧ 0 < j
  · rw [taoSection7SourceFThreeFactor, dif_pos h]
    exact norm_taoSection7FThree_le_one
      n xi (taoSection7PairX n ⟨j, h.2⟩ (Int.ofNat (s + b)))
  · rw [taoSection7SourceFThreeFactor, dif_neg h]

theorem taoSection7SourceFThreeFactor_hit_bound
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∀ j s b,
      b = 3 ∧ taoSection7SourceWhiteW n xi epsilon j (Int.ofNat (s + b)) →
        taoSection7SourceFThreeFactor n xi j s b ≤
          Real.exp (-(epsilon ^ 3)) := by
  intro j s b hhit
  rcases hhit with ⟨hb, hj, hwhite⟩
  unfold taoSection7SourceFThreeFactor
  rw [dif_pos ⟨hb, hj⟩]
  exact norm_taoSection7FThree_point_le_exp_neg_cube_of_white
    n xi ⟨j, hj⟩ (Int.ofNat (s + b)) hepsilon0 hepsilon1 hwhite

end Tao

end Erdos1135Predecessor
