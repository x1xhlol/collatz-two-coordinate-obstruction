/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Boundary
import Erdos1135Predecessor.Tao.Renewal.Prop78Case1Scalar

open scoped BigOperators Topology

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

private theorem one_sub_inv_le_exp_two_mul_case2
    {x : ℝ} (hx : 0 ≤ x) (hxhalf : 2 * x ≤ 1) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hden : 0 < 1 - x := by linarith
  calc
    (1 - x)⁻¹ ≤ 1 + 2 * x := (inv_le_iff_one_le_mul₀ hden).2 (by
      nlinarith [mul_nonneg hx (by linarith : 0 ≤ 1 - 2 * x)])
    _ = 2 * x + 1 := by ring
    _ ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)

theorem taoSection7Geom4ExpMoment_le_exp_eight_mul
    {t : ℝ} (ht0 : 0 ≤ t) (htsmall : 8 * t ≤ 1) :
    3 * Real.exp t < 4 ∧
      taoSection7Geom4ExpMoment t ≤ Real.exp (8 * t) := by
  have ht1 : t < 1 := by linarith
  have hden1 : 0 < 1 - t := by linarith
  have hexpInv : Real.exp t ≤ (1 - t)⁻¹ := by
    simpa [one_div] using
      Real.exp_bound_div_one_sub_of_interval ht0 ht1
  have hinv87 : (1 - t)⁻¹ ≤ (8 / 7 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hden1]
    nlinarith
  have hadm : 3 * Real.exp t < 4 := by
    nlinarith [hexpInv.trans hinv87]
  have hdenM : 0 < 4 - 3 * Real.exp t := by linarith
  have hden4 : 0 < 1 - 4 * t := by linarith
  have hprod : Real.exp t * (1 - t) ≤ 1 := by
    calc
      Real.exp t * (1 - t) ≤ (1 - t)⁻¹ * (1 - t) := by
        exact mul_le_mul_of_nonneg_right hexpInv hden1.le
      _ = 1 := by field_simp
  have hmgfInv :
      taoSection7Geom4ExpMoment t ≤ (1 - 4 * t)⁻¹ := by
    rw [taoSection7Geom4ExpMoment_eq hadm]
    rw [show (1 - 4 * t)⁻¹ = 1 / (1 - 4 * t) by
      rw [one_div]]
    rw [div_le_div_iff₀ hdenM hden4]
    nlinarith
  have hinvExp : (1 - 4 * t)⁻¹ ≤ Real.exp (8 * t) := by
    simpa only [show 2 * (4 * t) = 8 * t by ring] using
      one_sub_inv_le_exp_two_mul_case2
        (show 0 ≤ 4 * t by positivity) (by nlinarith)
  exact ⟨hadm, hmgfInv.trans hinvExp⟩

end

end Tao

end Erdos1135Predecessor
