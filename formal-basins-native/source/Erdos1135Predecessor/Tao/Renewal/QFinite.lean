/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldPoint
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSection7QWhiteIndicator
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint) : ℕ := by
  classical
  exact if W p then 1 else 0

noncomputable def taoSection7QWhiteFactor
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) : ℝ := by
  classical
  exact if W p then Real.exp (-(epsilon ^ 3)) else 1

theorem taoSection7QWhiteFactor_eq_exp_indicator
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QWhiteFactor epsilon W p =
      Real.exp (-(epsilon ^ 3) * (taoSection7QWhiteIndicator W p : ℝ)) := by
  classical
  by_cases hp : W p
  · simp [taoSection7QWhiteFactor, taoSection7QWhiteIndicator, hp]
  · simp [taoSection7QWhiteFactor, taoSection7QWhiteIndicator, hp]

theorem taoSection7QWhiteFactor_nonneg
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7QWhiteFactor epsilon W p := by
  rw [taoSection7QWhiteFactor_eq_exp_indicator]
  exact Real.exp_nonneg _

theorem taoSection7QWhiteFactor_le_one
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint) :
    taoSection7QWhiteFactor epsilon W p ≤ 1 := by
  rw [taoSection7QWhiteFactor_eq_exp_indicator]
  refine Real.exp_le_one_iff.mpr ?_
  have hpow : 0 ≤ epsilon ^ 3 := pow_nonneg hepsilon 3
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpow) (Nat.cast_nonneg _)

noncomputable def taoSection7QWhiteVisitCount
    (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7RenewalPoint → List TaoSection7RenewalPoint → ℕ
  | p, [] => taoSection7QWhiteIndicator W p
  | p, h :: hs =>
      taoSection7QWhiteIndicator W p +
        taoSection7QWhiteVisitCount W (p + h) hs

noncomputable def taoSection7QFinite
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7RenewalPoint → List TaoSection7RenewalPoint → ℝ
  | p, [] => taoSection7QWhiteFactor epsilon W p
  | p, h :: hs =>
      taoSection7QWhiteFactor epsilon W p *
        taoSection7QFinite epsilon W (p + h) hs

theorem taoSection7QFinite_nil
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QFinite epsilon W p [] =
      taoSection7QWhiteFactor epsilon W p :=
  rfl

theorem taoSection7QFinite_cons
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint) :
    taoSection7QFinite epsilon W p (h :: hs) =
      taoSection7QWhiteFactor epsilon W p *
        taoSection7QFinite epsilon W (p + h) hs :=
  rfl

theorem taoSection7QFinite_eq_exp_count
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    ∀ p holds,
      taoSection7QFinite epsilon W p holds =
        Real.exp (-(epsilon ^ 3) *
          (taoSection7QWhiteVisitCount W p holds : ℝ)) := by
  intro p holds
  induction holds generalizing p with
  | nil =>
      simp [taoSection7QFinite, taoSection7QWhiteVisitCount,
        taoSection7QWhiteFactor_eq_exp_indicator]
  | cons h hs ih =>
      rw [taoSection7QFinite_cons, ih]
      rw [taoSection7QWhiteFactor_eq_exp_indicator, ← Real.exp_add]
      congr 1
      simp [taoSection7QWhiteVisitCount, Nat.cast_add]
      ring

theorem taoSection7QFinite_nonneg
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) (holds : List TaoSection7RenewalPoint) :
    0 ≤ taoSection7QFinite epsilon W p holds := by
  rw [taoSection7QFinite_eq_exp_count]
  exact Real.exp_nonneg _

theorem taoSection7QFinite_le_one
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) (holds : List TaoSection7RenewalPoint) :
    taoSection7QFinite epsilon W p holds ≤ 1 := by
  rw [taoSection7QFinite_eq_exp_count]
  refine Real.exp_le_one_iff.mpr ?_
  have hpow : 0 ≤ epsilon ^ 3 := pow_nonneg hepsilon 3
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpow) (Nat.cast_nonneg _)

end Tao

end Erdos1135Predecessor
