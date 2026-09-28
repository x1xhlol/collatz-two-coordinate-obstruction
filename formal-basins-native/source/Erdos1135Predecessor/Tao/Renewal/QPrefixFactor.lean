/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QFinite
import Erdos1135Predecessor.Tao.Renewal.RenewalPathBasic
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection7QPrefixFactor
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    TaoSection7RenewalPoint → List TaoSection7RenewalPoint → ℝ
  | _p, [] => 1
  | p, h :: hs =>
      taoSection7QWhiteFactor epsilon W p *
        taoSection7QPrefixFactor epsilon W (p + h) hs

@[simp] theorem taoSection7QPrefixFactor_nil
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    taoSection7QPrefixFactor epsilon W p [] = 1 :=
  rfl

@[simp] theorem taoSection7QPrefixFactor_cons
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint) :
    taoSection7QPrefixFactor epsilon W p (h :: hs) =
      taoSection7QWhiteFactor epsilon W p *
        taoSection7QPrefixFactor epsilon W (p + h) hs :=
  rfl

theorem taoSection7QPrefixFactor_nonneg
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    ∀ (p : TaoSection7RenewalPoint) (pre : List TaoSection7RenewalPoint),
      0 ≤ taoSection7QPrefixFactor epsilon W p pre := by
  intro p pre
  induction pre generalizing p with
  | nil => simp [taoSection7QPrefixFactor]
  | cons h hs ih =>
      rw [taoSection7QPrefixFactor_cons]
      exact mul_nonneg
        (taoSection7QWhiteFactor_nonneg epsilon W p) (ih (p + h))

theorem taoSection7QPrefixFactor_le_one
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) :
    ∀ (p : TaoSection7RenewalPoint) (pre : List TaoSection7RenewalPoint),
      taoSection7QPrefixFactor epsilon W p pre ≤ 1 := by
  intro p pre
  induction pre generalizing p with
  | nil => simp [taoSection7QPrefixFactor]
  | cons h hs ih =>
      rw [taoSection7QPrefixFactor_cons]
      calc
        taoSection7QWhiteFactor epsilon W p *
            taoSection7QPrefixFactor epsilon W (p + h) hs ≤
            taoSection7QWhiteFactor epsilon W p * 1 :=
          mul_le_mul_of_nonneg_left (ih (p + h))
            (taoSection7QWhiteFactor_nonneg epsilon W p)
        _ ≤ 1 := by
          simpa using taoSection7QWhiteFactor_le_one hepsilon W p

theorem taoSection7RenewalPathPoint_length_cons
    (p h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint) :
    taoSection7RenewalPathPoint p (h :: hs) (h :: hs).length =
      taoSection7RenewalPathPoint (p + h) hs hs.length := by
  simp [taoSection7RenewalPathPoint]

theorem taoSection7QFinite_append_eq_prefixFactor_mul_endpoint
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    ∀ (p : TaoSection7RenewalPoint)
      (pre tail : List TaoSection7RenewalPoint),
      taoSection7QFinite epsilon W p (pre ++ tail) =
        taoSection7QPrefixFactor epsilon W p pre *
          taoSection7QFinite epsilon W
            (taoSection7RenewalPathPoint p pre pre.length) tail := by
  intro p pre
  induction pre generalizing p with
  | nil =>
      intro tail
      simp [taoSection7RenewalPathPoint, taoSection7QPrefixFactor]
  | cons h hs ih =>
      intro tail
      rw [List.cons_append, taoSection7QFinite_cons,
        taoSection7QPrefixFactor_cons, ih (p + h) tail,
        taoSection7RenewalPathPoint_length_cons]
      ring

end

end Tao

end Erdos1135Predecessor
