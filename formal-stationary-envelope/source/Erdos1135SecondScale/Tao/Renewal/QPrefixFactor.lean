/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QFinite
import Erdos1135SecondScale.Tao.Renewal.RenewalPathBasic
import Mathlib.Tactic

/-!
# Section 7 Stopped Prefix Factors

This low proof leaf separates the white factors before a stopped endpoint
from the `Q` value beginning at that endpoint.  It supplies the deterministic
product identity needed by Tao's stopped recursion `(7.45)`; no stopping-law
expectation or Proposition 7.8 estimate is proved here.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Product of white factors at the points strictly before the endpoint of a
finite Hold-increment prefix.  In particular, the empty prefix has factor one. -/
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
  | nil => simp
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
  | nil => simp
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

/-- On a nonempty stopped prefix, the endpoint-exclusive product is the old
`QFinite` product on `dropLast`. -/
theorem taoSection7QPrefixFactor_eq_QFinite_dropLast
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    ∀ pre : List TaoSection7RenewalPoint, pre ≠ [] →
      taoSection7QPrefixFactor epsilon W p pre =
        taoSection7QFinite epsilon W p pre.dropLast := by
  intro pre hpre
  induction pre generalizing p with
  | nil => exact (hpre rfl).elim
  | cons h hs ih =>
      cases hs with
      | nil => simp [taoSection7QFinite]
      | cons h' hs =>
          rw [taoSection7QPrefixFactor_cons,
            List.dropLast_cons_of_ne_nil (by simp),
            taoSection7QFinite_cons]
          congr 1
          exact ih (p + h) (by simp)

/-- The path point after consuming an entire prefix is its recursive endpoint. -/
theorem taoSection7RenewalPathPoint_length_cons
    (p h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint) :
    taoSection7RenewalPathPoint p (h :: hs) (h :: hs).length =
      taoSection7RenewalPathPoint (p + h) hs hs.length := by
  simp [taoSection7RenewalPathPoint]

/-- Exact finite stopped-product factorization.

The prefix factor contains precisely the visits with indices `0, ..., K-1`;
the endpoint factor is the first factor in the remaining `QFinite` term.
-/
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
      simp [taoSection7RenewalPathPoint]
  | cons h hs ih =>
      intro tail
      rw [List.cons_append, taoSection7QFinite_cons,
        taoSection7QPrefixFactor_cons, ih (p + h) tail,
        taoSection7RenewalPathPoint_length_cons]
      ring

/-- A stopped prefix followed by the empty tail includes the endpoint factor
only in `QFinite`, never in the prefix factor. -/
theorem taoSection7QFinite_eq_prefixFactor_mul_endpointWhiteFactor
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) (pre : List TaoSection7RenewalPoint) :
    taoSection7QFinite epsilon W p pre =
      taoSection7QPrefixFactor epsilon W p pre *
        taoSection7QWhiteFactor epsilon W
          (taoSection7RenewalPathPoint p pre pre.length) := by
  simpa using
    (taoSection7QFinite_append_eq_prefixFactor_mul_endpoint
      epsilon W p pre [])

end

end Tao
end Erdos1135SecondScale
