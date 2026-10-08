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
import Mathlib.Data.Finset.Preimage
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open scoped BigOperators

@[simp]
theorem card_taoSection7IntIccWindow (R : ℕ) (c : ℤ) :
    (taoSection7IntIccWindow R c).card = 2 * R + 1 := by
  rw [taoSection7IntIccWindow, Int.card_Icc]
  omega

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

end Erdos1135Predecessor
