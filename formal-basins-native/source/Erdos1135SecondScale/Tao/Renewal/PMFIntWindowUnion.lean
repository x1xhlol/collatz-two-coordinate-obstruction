/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.SeparatedWindowSum
import Mathlib.Data.Finset.Preimage
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Countable PMF Bounds for Integer-Window Unions

This neutral proof leaf bounds a countable union of finite integer-coordinate
windows by overcounting every window separately.  It does not require the
windows to be disjoint; their exact cardinality contributes the factor
`2 * R + 1`.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open scoped BigOperators

/-- A closed integer window of radius `R` contains exactly `2 * R + 1`
integers. -/
@[simp]
theorem card_taoSection7IntIccWindow (R : ℕ) (c : ℤ) :
    (taoSection7IntIccWindow R c).card = 2 * R + 1 := by
  rw [taoSection7IntIccWindow, Int.card_Icc]
  omega

/-- Countably many radius-`R` coordinate windows may be overcounted one
window at a time.  Injectivity of `coord` bounds each window fiber by the
window cardinality; no separation condition on the centers is needed. -/
theorem taoSection7PMF_intIccWindowUnion_outerMeasure_le
    {α : Type*} (pmf : PMF α) (coord : α → ℤ)
    (hcoord : Function.Injective coord)
    (centers : Set ℤ) (R : ℕ) (bound : ℤ → ENNReal)
    (hpoint : ∀ c : centers, ∀ x : α,
      coord x ∈ taoSection7IntIccWindow R c.1 →
        pmf x ≤ bound c.1) :
    pmf.toOuterMeasure
        {x | ∃ c : centers,
          coord x ∈ taoSection7IntIccWindow R c.1} ≤
      ((2 * R + 1 : ℕ) : ENNReal) *
        ∑' c : centers, bound c.1 := by
  classical
  have hevent :
      {x | ∃ c : centers,
          coord x ∈ taoSection7IntIccWindow R c.1} =
        ⋃ c : centers,
          coord ⁻¹' (↑(taoSection7IntIccWindow R c.1) : Set ℤ) := by
    ext x
    simp
  rw [hevent]
  calc
    pmf.toOuterMeasure
        (⋃ c : centers,
          coord ⁻¹' (↑(taoSection7IntIccWindow R c.1) : Set ℤ)) ≤
      ∑' c : centers,
        pmf.toOuterMeasure
          (coord ⁻¹' (↑(taoSection7IntIccWindow R c.1) : Set ℤ)) :=
      MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' c : centers,
        ((2 * R + 1 : ℕ) : ENNReal) * bound c.1 := by
      apply ENNReal.tsum_le_tsum
      intro c
      let window := taoSection7IntIccWindow R c.1
      let fiber := window.preimage coord hcoord.injOn
      have hcard : fiber.card ≤ 2 * R + 1 := by
        have hmaps : Set.MapsTo coord (↑fiber : Set α) (↑window : Set ℤ) := by
          intro x hx
          simpa [fiber] using hx
        have hle : fiber.card ≤ window.card :=
          Finset.card_le_card_of_injOn coord hmaps hcoord.injOn
        simpa [window] using hle
      calc
        pmf.toOuterMeasure
            (coord ⁻¹' (↑(taoSection7IntIccWindow R c.1) : Set ℤ)) =
          pmf.toOuterMeasure (↑fiber : Set α) := by
            simp [fiber, window]
        _ = ∑ x ∈ fiber, pmf x := pmf.toOuterMeasure_apply_finset fiber
        _ ≤ ∑ x ∈ fiber, bound c.1 := by
          apply Finset.sum_le_sum
          intro x hx
          apply hpoint c x
          simpa [fiber, window] using hx
        _ = (fiber.card : ENNReal) * bound c.1 := by simp
        _ ≤ ((2 * R + 1 : ℕ) : ENNReal) * bound c.1 := by
          gcongr
    _ = ((2 * R + 1 : ℕ) : ENNReal) *
        ∑' c : centers, bound c.1 := by
      rw [ENNReal.tsum_mul_left]

end

end Tao
end Erdos1135SecondScale
