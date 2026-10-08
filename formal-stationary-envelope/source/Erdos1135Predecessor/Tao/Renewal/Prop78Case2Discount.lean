/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageEndpoint
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoSection7Prop78_exp_neg_epsilon_cube_half_le
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    Real.exp (-(epsilon ^ 3 / 2)) ≤ 1 - epsilon ^ 3 / 4 := by
  let x : ℝ := epsilon ^ 3 / 2
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hepsilonCube : epsilon ^ 3 ≤ 1 := by
    exact pow_le_one₀ hepsilon0 hepsilon1
  have hx1 : x ≤ 1 := by
    dsimp [x]
    linarith
  have hden : 0 < 1 + x := by linarith
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) hden).2 (by
      simpa [add_comm] using Real.add_one_le_exp x)
  have hinv : (1 + x)⁻¹ ≤ 1 - x / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  calc
    Real.exp (-(epsilon ^ 3 / 2)) = Real.exp (-x) := by rfl
    _ ≤ (1 + x)⁻¹ := hexp
    _ ≤ 1 - x / 2 := hinv
    _ = 1 - epsilon ^ 3 / 4 := by
      dsimp [x]
      ring

theorem pmf_eventMass_toReal_eq_tsum_indicator
    {alpha : Type*} (p : PMF alpha) (E : Set alpha) :
    (p.toOuterMeasure E).toReal =
      ∑' x : alpha, E.indicator (fun x => (p x).toReal) x := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases hx : x ∈ E <;> simp [Set.indicator, hx]
  · intro x
    by_cases hx : x ∈ E <;>
      simp [Set.indicator, hx, PMF.apply_ne_top p x]

theorem pmf_discounted_exp_expectation_le_sub_eventMass
    {alpha : Type*} (p : PMF alpha) (E : Set alpha)
    (g : alpha → ℝ) {d c : ℝ}
    (hc0 : 0 ≤ c) (hdiscount : Real.exp (-d) ≤ 1 - c)
    (hg0 : ∀ x, 0 ≤ g x)
    (hsum : Summable fun x : alpha => (p x).toReal * Real.exp (g x)) :
    (∑' x : alpha,
        (p x).toReal *
          (Real.exp (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
            Real.exp (g x))) ≤
      (∑' x : alpha, (p x).toReal * Real.exp (g x)) -
        c * (p.toOuterMeasure E).toReal := by
  classical
  let base : alpha → ℝ := fun x => (p x).toReal * Real.exp (g x)
  let discounted : alpha → ℝ := fun x =>
    (p x).toReal *
      (Real.exp (-(d * E.indicator (fun _ => (1 : ℝ)) x)) *
        Real.exp (g x))
  let eventTerm : alpha → ℝ := fun x =>
    c * E.indicator (fun x => (p x).toReal) x
  have hdiscounted0 : ∀ x, 0 ≤ discounted x := by
    intro x
    dsimp [discounted]
    positivity
  have hdiscounted_le : ∀ x, discounted x ≤ base x := by
    intro x
    dsimp [discounted, base]
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_mem hx, mul_one]
      have hfactor : Real.exp (-d) ≤ 1 :=
        hdiscount.trans (sub_le_self 1 hc0)
      have hinner :
          Real.exp (-d) * Real.exp (g x) ≤ Real.exp (g x) := by
        calc
          Real.exp (-d) * Real.exp (g x) ≤ 1 * Real.exp (g x) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
          _ = Real.exp (g x) := one_mul _
      exact mul_le_mul_of_nonneg_left hinner ENNReal.toReal_nonneg
    · simp [Set.indicator, hx]
  have hdiscountedSum : Summable discounted :=
    Summable.of_nonneg_of_le hdiscounted0 hdiscounted_le (by
      simpa [base] using hsum)
  have hpSum : Summable fun x : alpha => (p x).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have heventSum : Summable eventTerm := by
    have hi := hpSum.indicator E
    refine (hi.mul_left c).congr ?_
    intro x
    simp only [eventTerm]
  have hpoint : ∀ x, discounted x + eventTerm x ≤ base x := by
    intro x
    have hp0 : 0 ≤ (p x).toReal := ENNReal.toReal_nonneg
    by_cases hx : x ∈ E
    · have heg : 1 ≤ Real.exp (g x) := Real.one_le_exp (hg0 x)
      have hscalar :
          Real.exp (-d) * Real.exp (g x) + c ≤ Real.exp (g x) := by
        calc
          Real.exp (-d) * Real.exp (g x) + c ≤
              (1 - c) * Real.exp (g x) + c := by
            gcongr
          _ ≤ Real.exp (g x) := by
            nlinarith [mul_nonneg hc0 (sub_nonneg.mpr heg)]
      dsimp [discounted, eventTerm, base]
      simp only [Set.indicator_of_mem hx, mul_one]
      calc
        (p x).toReal * (Real.exp (-d) * Real.exp (g x)) +
            c * (p x).toReal =
            (p x).toReal *
              (Real.exp (-d) * Real.exp (g x) + c) := by ring
        _ ≤ (p x).toReal * Real.exp (g x) :=
          mul_le_mul_of_nonneg_left hscalar hp0
    · dsimp [discounted, eventTerm, base]
      simp [Set.indicator, hx]
  have htotal :
      (∑' x : alpha, discounted x) + ∑' x : alpha, eventTerm x ≤
        ∑' x : alpha, base x := by
    rw [← hdiscountedSum.tsum_add heventSum]
    exact (hdiscountedSum.add heventSum).tsum_le_tsum hpoint (by
      simpa [base] using hsum)
  have heventMass :
      (∑' x : alpha, eventTerm x) = c * (p.toOuterMeasure E).toReal := by
    calc
      (∑' x : alpha, eventTerm x) =
          c * ∑' x : alpha, E.indicator (fun x => (p x).toReal) x := by
        rw [← tsum_mul_left]
      _ = c * (p.toOuterMeasure E).toReal := by
        rw [pmf_eventMass_toReal_eq_tsum_indicator]
  dsimp [discounted, base] at htotal ⊢
  rw [heventMass] at htotal
  linarith

end

end Tao

end Erdos1135Predecessor
