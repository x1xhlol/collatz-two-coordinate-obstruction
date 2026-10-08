/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# True Proportional-Reference Absorption

This neutral leaf absorbs a small multiple of a comparison reference without
deleting that reference from the left-hand side.  Its finite endpoint form is
designed for the post-D6 A5 cell inequalities.
-/

namespace Erdos1135
namespace ND

/-- A discrepancy bounded by an error plus at most half of its reference can
be rewritten against the actual value.  No sign condition on the actual
value, reference, or error is needed. -/
theorem abs_sub_le_trueAbsorb
    {X R a e : ℝ}
    (ha0 : 0 ≤ a) (haHalf : a ≤ 1 / 2)
    (h : |X - R| ≤ e + a * R) :
    |X - R| ≤ 2 * a * X + 2 * e := by
  have hRX : R - X ≤ |X - R| := by
    calc
      R - X ≤ |R - X| := le_abs_self _
      _ = |X - R| := abs_sub_comm R X
  have hRle : R ≤ X + |X - R| := by
    linarith
  have haRle : a * R ≤ a * (X + |X - R|) :=
    mul_le_mul_of_nonneg_left hRle ha0
  have htwoa : 2 * a ≤ 1 := by
    linarith
  have hcontract : (2 * a) * |X - R| ≤ |X - R| := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right htwoa (abs_nonneg (X - R))
  nlinarith

/-- Finite componentwise true absorption with cell-dependent coefficients
bounded by one common half-coefficient.  The common reference sum remains on
the left. -/
theorem abs_sum_sub_sum_le_trueAbsorb
    {ι : Type*} (s : Finset ι)
    (X R e a : ι → ℝ) (aBar : ℝ)
    (hX : ∀ i ∈ s, 0 ≤ X i)
    (ha0 : ∀ i ∈ s, 0 ≤ a i)
    (haBar : ∀ i ∈ s, a i ≤ aBar)
    (haBarHalf : aBar ≤ 1 / 2)
    (hcell : ∀ i ∈ s, |X i - R i| ≤ e i + a i * R i) :
    |(∑ i ∈ s, X i) - ∑ i ∈ s, R i| ≤
      2 * aBar * (∑ i ∈ s, X i) + 2 * ∑ i ∈ s, e i := by
  have hpoint : ∀ i ∈ s,
      |X i - R i| ≤ 2 * aBar * X i + 2 * e i := by
    intro i hi
    have hiAbs := abs_sub_le_trueAbsorb
      (ha0 i hi) ((haBar i hi).trans haBarHalf) (hcell i hi)
    have hscale : a i * X i ≤ aBar * X i :=
      mul_le_mul_of_nonneg_right (haBar i hi) (hX i hi)
    linarith
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s, (X i - R i)| ≤
        ∑ i ∈ s, |X i - R i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (2 * aBar * X i + 2 * e i) := by
      exact Finset.sum_le_sum fun i hi => hpoint i hi
    _ = 2 * aBar * (∑ i ∈ s, X i) + 2 * ∑ i ∈ s, e i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Endpoint-shaped finite absorption.  Each cell is already compared with
`q i * R i`, and the same single endpoint factor scales its residual error.
No second endpoint factor is introduced. -/
theorem abs_sum_sub_sum_mul_le_trueAbsorb
    {ι : Type*} (s : Finset ι)
    (Y q R e a : ι → ℝ) (aBar : ℝ)
    (hY : ∀ i ∈ s, 0 ≤ Y i)
    (ha0 : ∀ i ∈ s, 0 ≤ a i)
    (haBar : ∀ i ∈ s, a i ≤ aBar)
    (haBarHalf : aBar ≤ 1 / 2)
    (hcell : ∀ i ∈ s,
      |Y i - q i * R i| ≤ q i * (e i + a i * R i)) :
    |(∑ i ∈ s, Y i) - ∑ i ∈ s, q i * R i| ≤
      2 * aBar * (∑ i ∈ s, Y i) +
        2 * ∑ i ∈ s, q i * e i := by
  apply abs_sum_sub_sum_le_trueAbsorb s Y
    (fun i => q i * R i) (fun i => q i * e i) a aBar
      hY ha0 haBar haBarHalf
  intro i hi
  convert hcell i hi using 1; ring

end ND
end Erdos1135
