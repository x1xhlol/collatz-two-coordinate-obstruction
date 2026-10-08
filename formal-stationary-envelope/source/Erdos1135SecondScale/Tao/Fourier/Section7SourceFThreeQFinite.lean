/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.SourceListBridge
import Erdos1135SecondScale.Tao.Fourier.Section7Cancellation
import Mathlib.Tactic

/-!
# Section 7 Source `FThree` Product To QFinite

This module instantiates the deterministic source-block/QFinite bridge with the
source-native `f(x,3)` factors from the local Section 7 cancellation layer.  It
does not introduce weighted Hold masses or expectation estimates.
-/

namespace Erdos1135SecondScale
namespace Tao

/--
Source-white predicate in the native product-penalty shape. A nonpositive
time index is false because Tao's Section 7 points use positive `j`.
-/
def taoSection7SourceWhiteW
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    ℕ → ℤ → Prop :=
  fun j l =>
    ∃ hj : 0 < j,
      taoSection7White epsilon
        (taoSection7ThetaResidue n xi ⟨j, hj⟩ l)

/-- Public version of the unit-norm kernel fact used by Section 7. -/
theorem norm_taoForwardDFTKernel_eq_one
    {N : ℕ} [NeZero N] (x xi : ZMod N) :
    ‖taoForwardDFTKernel x xi‖ = 1 := by
  simp [taoForwardDFTKernel, ZMod.stdAddChar]

/-- The two-point conditional average at `b = 3` is bounded by `1`. -/
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

/-- The source-shaped conditional expectation `f(x,3)` is bounded by `1`. -/
theorem norm_taoSection7FThree_le_one
    (n : ℕ) (xi x : ZMod (3 ^ n)) :
    ‖taoSection7FThree n xi x‖ ≤ 1 := by
  rw [norm_taoSection7FThree_eq_pairAverage]
  exact norm_taoSection7PairAverage_le_one n xi x

/--
The source `b = 3` factor at product state `(j,s)`, using the post-step point
coordinate `(j, s+b)`. Non-`b = 3` and nonpositive-index placeholders are `1`.
-/
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

theorem taoSection7SourceFThreeFactorProduct_blocks_le_qfinite
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
        (taoSection7SourceBlocks (pre :: pres)) ≤
      taoSection7QFinite epsilon
        (taoSection7SourceWhiteRenewal (taoSection7SourceWhiteW n xi epsilon))
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  exact taoSection7FactorProduct_blocks_le_qfinite
    (taoSection7SourceFThreeFactor_nonneg n xi)
    (taoSection7SourceFThreeFactor_hit_bound n xi hepsilon0 hepsilon1)
    (by
      intro j s b _hmiss
      exact taoSection7SourceFThreeFactor_le_one n xi j s b)
    pre pres hpre hpres

end Tao
end Erdos1135SecondScale
