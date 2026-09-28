/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageExpMoment
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Discount
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2MomentScalar
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Pointwise
import Erdos1135Predecessor.Tao.Renewal.QStoppedEndpoint

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

theorem pmf_expectation_le_mul_sub_eventMass_of_branch_bounds
    {alpha : Type*} (p : PMF alpha) (E : Set alpha)
    (F g : alpha → ℝ) {C d c : ℝ}
    (hF0 : ∀ x, 0 ≤ F x)
    (hC0 : 0 ≤ C)
    (hc0 : 0 ≤ c)
    (hdiscount : Real.exp (-d) ≤ 1 - c)
    (hg0 : ∀ x, 0 ≤ g x)
    (hsum : Summable fun x => (p x).toReal * Real.exp (g x))
    (hordinary : ∀ x, p x ≠ 0 → F x ≤ C * Real.exp (g x))
    (hlocalized : ∀ x, p x ≠ 0 → x ∈ E →
      F x ≤ C * (Real.exp (-d) * Real.exp (g x))) :
    (∑' x, (p x).toReal * F x) ≤
      C * ((∑' x, (p x).toReal * Real.exp (g x)) -
        c * (p.toOuterMeasure E).toReal) := by
  classical
  let discounted : alpha → ℝ := fun x =>
    (p x).toReal *
      (Real.exp (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
        Real.exp (g x))
  let base : alpha → ℝ := fun x => (p x).toReal * Real.exp (g x)
  have hdiscount_le_one : Real.exp (-d) ≤ 1 :=
    hdiscount.trans (sub_le_self 1 hc0)
  have hdiscounted0 : ∀ x, 0 ≤ discounted x := by
    intro x
    dsimp [discounted]
    positivity
  have hdiscounted_le : ∀ x, discounted x ≤ base x := by
    intro x
    dsimp [discounted, base]
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_mem hx, mul_one]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact mul_le_of_le_one_left (Real.exp_nonneg _) hdiscount_le_one
    · simp [Set.indicator, hx]
  have hdiscountedSum : Summable discounted :=
    Summable.of_nonneg_of_le hdiscounted0 hdiscounted_le (by
      simpa [base] using hsum)
  have hmajor : ∀ x,
      (p x).toReal * F x ≤ C * discounted x := by
    intro x
    by_cases hp : p x = 0
    · simp [hp, discounted]
    · have hbranch : F x ≤ C *
          (Real.exp (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
            Real.exp (g x)) := by
        by_cases hx : x ∈ E
        · have hloc := hlocalized x hp hx
          simpa [Set.indicator, hx] using hloc
        · have hord := hordinary x hp
          simpa [Set.indicator, hx] using hord
      calc
        (p x).toReal * F x ≤ (p x).toReal *
            (C * (Real.exp
              (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
                Real.exp (g x))) :=
          mul_le_mul_of_nonneg_left hbranch ENNReal.toReal_nonneg
        _ = C * discounted x := by
          dsimp [discounted]
          ring
  have hactualSum : Summable fun x => (p x).toReal * F x :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (hF0 x)) hmajor
      (hdiscountedSum.mul_left C)
  have hdiscBound := pmf_discounted_exp_expectation_le_sub_eventMass
    p E g hc0 hdiscount hg0 hsum
  calc
    (∑' x, (p x).toReal * F x) ≤
        ∑' x, C * discounted x :=
      hactualSum.tsum_le_tsum hmajor (hdiscountedSum.mul_left C)
    _ = C * ∑' x, discounted x := by rw [tsum_mul_left]
    _ ≤ C * ((∑' x, (p x).toReal * Real.exp (g x)) -
          c * (p.toOuterMeasure E).toReal) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      simpa [discounted] using hdiscBound

end

end Tao

end Erdos1135Predecessor
