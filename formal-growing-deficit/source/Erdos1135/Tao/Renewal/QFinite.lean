import Erdos1135.Tao.Renewal.HoldPoint
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Section 7 Finite Q Recursion

This module records deterministic finite products for Tao's Section 7 renewal
quantity `Q`.  It works over already-defined renewal points and finite lists of
holding increments.  It does not define the law of `Hold`, take expectations,
or prove the asymptotic renewal estimate.
-/

namespace Erdos1135
namespace Tao

/-- Indicator of a white visit in the finite `Q` recursion. -/
noncomputable def taoSection7QWhiteIndicator
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint) : ℕ := by
  classical
  exact if W p then 1 else 0

/--
The local multiplicative factor in Tao equation `(7.35)`:
`exp(-epsilon^3 * 1_W(p))`.
-/
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

/--
Finite white-visit count along the path
`p, p + h_1, p + h_1 + h_2, ...`.
-/
noncomputable def taoSection7QWhiteVisitCount
    (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7RenewalPoint → List TaoSection7RenewalPoint → ℕ
  | p, [] => taoSection7QWhiteIndicator W p
  | p, h :: hs =>
      taoSection7QWhiteIndicator W p +
        taoSection7QWhiteVisitCount W (p + h) hs

/--
Finite truncation of Tao's `Q(j,l)`: multiply the white factors at the current
point and along the following finite list of holding-time increments.
-/
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

/--
Finite version of the recursive formula `(7.35)`.  The empty tail is the finite
truncation boundary.
-/
theorem taoSection7QFinite_eq_factor_mul_next
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) (holds : List TaoSection7RenewalPoint) :
    taoSection7QFinite epsilon W p holds =
      taoSection7QWhiteFactor epsilon W p *
        match holds with
        | [] => 1
        | h :: hs => taoSection7QFinite epsilon W (p + h) hs := by
  cases holds with
  | nil =>
      simp [taoSection7QFinite]
  | cons _h _hs =>
      rfl

/-- The finite `Q` product is exactly the exponential of the finite visit count. -/
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
end Erdos1135
