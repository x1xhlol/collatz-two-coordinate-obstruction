/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.HoldExpectation
import Erdos1135SecondScale.Tao.Renewal.HoldIID
import Mathlib.Tactic

/-!
# Section 7 Q Expectation Vocabulary

This module adds finite-support and full-Hold expectation vocabulary for a
supplied Section 7 `Q` function.  It deliberately avoids proving existence of a
bounded fixed point: `Q := 0` would make such an existence theorem vacuous and
would not be Tao's actual infinite product.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

def TaoSection7QBounded01
    (Q : TaoSection7RenewalPoint → ℝ) : Prop :=
  ∀ p, 0 ≤ Q p ∧ Q p ≤ 1

/-- Finite expectation over a chosen support set of single Hold increments. -/
noncomputable def taoSection7HoldExpectationOn
    (S : Finset TaoSection7RenewalPoint)
    (F : TaoSection7RenewalPoint → ℝ) : ℝ :=
  ∑ h ∈ S, (taoSection7HoldPMF h).toReal * F h

noncomputable def taoSection7QRecursionRHSOn
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (S : Finset TaoSection7RenewalPoint)
    (Q : TaoSection7RenewalPoint → ℝ)
    (p : TaoSection7RenewalPoint) : ℝ :=
  taoSection7QWhiteFactor epsilon W p *
    taoSection7HoldExpectationOn S (fun h => Q (p + h))

def TaoSection7QRecursionOn
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (S : Finset TaoSection7RenewalPoint)
    (Q : TaoSection7RenewalPoint → ℝ) : Prop :=
  TaoSection7QBounded01 Q ∧
    ∀ p, Q p = taoSection7QRecursionRHSOn epsilon W S Q p

theorem taoSection7HoldExpectationOn_nonneg
    {S : Finset TaoSection7RenewalPoint}
    {F : TaoSection7RenewalPoint → ℝ}
    (hF : ∀ h ∈ S, 0 ≤ F h) :
    0 ≤ taoSection7HoldExpectationOn S F := by
  classical
  unfold taoSection7HoldExpectationOn
  exact Finset.sum_nonneg (by
    intro h hS
    exact mul_nonneg ENNReal.toReal_nonneg (hF h hS))

theorem taoSection7HoldExpectationOn_le_mass
    {S : Finset TaoSection7RenewalPoint}
    {F : TaoSection7RenewalPoint → ℝ}
    (hF1 : ∀ h ∈ S, F h ≤ 1) :
    taoSection7HoldExpectationOn S F ≤
      ∑ h ∈ S, (taoSection7HoldPMF h).toReal := by
  classical
  unfold taoSection7HoldExpectationOn
  exact Finset.sum_le_sum (by
    intro h hS
    have hmass : 0 ≤ (taoSection7HoldPMF h).toReal := ENNReal.toReal_nonneg
    calc
      (taoSection7HoldPMF h).toReal * F h
          ≤ (taoSection7HoldPMF h).toReal * 1 := by
            exact mul_le_mul_of_nonneg_left (hF1 h hS) hmass
      _ = (taoSection7HoldPMF h).toReal := by ring)

theorem taoSection7QRecursionRHSOn_nonneg
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (S : Finset TaoSection7RenewalPoint)
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7QRecursionRHSOn epsilon W S Q p := by
  unfold taoSection7QRecursionRHSOn
  exact mul_nonneg
    (taoSection7QWhiteFactor_nonneg epsilon W p)
    (taoSection7HoldExpectationOn_nonneg (by
      intro h _hS
      exact (hQ (p + h)).1))

theorem taoSection7QRecursionRHSOn_le_one_of_mass_le_one
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (S : Finset TaoSection7RenewalPoint)
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (p : TaoSection7RenewalPoint)
    (hS : (∑ h ∈ S, (taoSection7HoldPMF h).toReal) ≤ 1) :
    taoSection7QRecursionRHSOn epsilon W S Q p ≤ 1 := by
  unfold taoSection7QRecursionRHSOn
  have hExp_nonneg :
      0 ≤ taoSection7HoldExpectationOn S (fun h => Q (p + h)) :=
    taoSection7HoldExpectationOn_nonneg (by
      intro h _hS
      exact (hQ (p + h)).1)
  have hExp_le_one :
      taoSection7HoldExpectationOn S (fun h => Q (p + h)) ≤ 1 := by
    exact
      (taoSection7HoldExpectationOn_le_mass (by
        intro h _hS
        exact (hQ (p + h)).2)).trans hS
  calc
    taoSection7QWhiteFactor epsilon W p *
        taoSection7HoldExpectationOn S (fun h => Q (p + h))
        ≤ 1 * 1 := by
          exact mul_le_mul
            (taoSection7QWhiteFactor_le_one hepsilon0 W p)
            hExp_le_one hExp_nonneg (by norm_num)
    _ = 1 := by norm_num

noncomputable def taoSection7FullHoldQRecursionRHS
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (Q : TaoSection7RenewalPoint → ℝ)
    (p : TaoSection7RenewalPoint) : ℝ :=
  taoSection7QWhiteFactor epsilon W p *
    taoSection7HoldExpectationFull (fun h => Q (p + h))

theorem taoSection7FullHoldQRecursionRHS_nonneg
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7FullHoldQRecursionRHS epsilon W Q p := by
  unfold taoSection7FullHoldQRecursionRHS
  exact mul_nonneg
    (taoSection7QWhiteFactor_nonneg epsilon W p)
    (taoSection7HoldExpectationFull_nonneg_of_nonneg (by
      intro h
      exact (hQ (p + h)).1))

theorem taoSection7FullHoldQRecursionRHS_le_one
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7QBounded01 Q)
    (p : TaoSection7RenewalPoint) :
    taoSection7FullHoldQRecursionRHS epsilon W Q p ≤ 1 := by
  unfold taoSection7FullHoldQRecursionRHS
  have hExp_nonneg :
      0 ≤ taoSection7HoldExpectationFull (fun h => Q (p + h)) :=
    taoSection7HoldExpectationFull_nonneg_of_nonneg (by
      intro h
      exact (hQ (p + h)).1)
  have hExp_le_one :
      taoSection7HoldExpectationFull (fun h => Q (p + h)) ≤ 1 :=
    taoSection7HoldExpectationFull_le_one_of_bounded01
      (by
        intro h
        exact (hQ (p + h)).1)
      (by
        intro h
        exact (hQ (p + h)).2)
  calc
    taoSection7QWhiteFactor epsilon W p *
        taoSection7HoldExpectationFull (fun h => Q (p + h))
        ≤ 1 * 1 := by
          exact mul_le_mul
            (taoSection7QWhiteFactor_le_one hepsilon0 W p)
            hExp_le_one hExp_nonneg (by norm_num)
    _ = 1 := by norm_num

end Tao
end Erdos1135SecondScale
