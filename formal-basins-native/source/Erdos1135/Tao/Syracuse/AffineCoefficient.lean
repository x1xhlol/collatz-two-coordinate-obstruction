import Erdos1135.Tao.Syracuse.AffineTrajectory

/-!
# Syracuse Affine Coefficient Bounds

This neutral leaf bounds the real affine main coefficient while retaining its
`(3/4)^q` contraction. Offset nonnegativity and offset envelopes remain in
their existing owners and are not folded into these lemmas.
-/

namespace Erdos1135
namespace Tao

private theorem log_two_pos_coefficient :
    0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

private theorem log_three_four_eq :
    Real.log (3 / 4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  norm_num

private theorem three_four_pow_eq_exp (q : ℕ) :
    (3 / 4 : ℝ) ^ q =
      Real.exp ((q : ℝ) * Real.log (3 / 4 : ℝ)) := by
  calc
    (3 / 4 : ℝ) ^ q =
        (Real.exp (Real.log (3 / 4 : ℝ))) ^ q := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 4)]
    _ = Real.exp ((q : ℝ) * Real.log (3 / 4 : ℝ)) := by
      rw [← Real.exp_nat_mul]

private theorem three_pow_div_two_pow_eq_exp (q w : ℕ) :
    (3 : ℝ) ^ q / (2 : ℝ) ^ w =
      Real.exp ((q : ℝ) * Real.log 3 - (w : ℝ) * Real.log 2) := by
  have hcoeffPos : 0 < (3 : ℝ) ^ q / (2 : ℝ) ^ w := by positivity
  calc
    (3 : ℝ) ^ q / (2 : ℝ) ^ w =
        Real.exp (Real.log ((3 : ℝ) ^ q / (2 : ℝ) ^ w)) :=
      (Real.exp_log hcoeffPos).symm
    _ = Real.exp ((q : ℝ) * Real.log 3 - (w : ℝ) * Real.log 2) := by
      congr 1
      rw [Real.log_div (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)), Real.log_pow, Real.log_pow]

/-- An upper weight bound gives a lower affine coefficient bound. -/
theorem exp_neg_log_two_mul_mul_three_four_pow_le_three_pow_div_two_pow
    {q w : ℕ} {H : ℝ}
    (hw : (w : ℝ) ≤ 2 * (q : ℝ) + H) :
    Real.exp (-Real.log 2 * H) * (3 / 4 : ℝ) ^ q ≤
      (3 : ℝ) ^ q / (2 : ℝ) ^ w := by
  have hmul :=
    mul_le_mul_of_nonneg_right hw log_two_pos_coefficient.le
  rw [three_four_pow_eq_exp, ← Real.exp_add,
    three_pow_div_two_pow_eq_exp]
  apply Real.exp_le_exp.mpr
  rw [log_three_four_eq]
  nlinarith

/-- A lower weight bound gives an upper affine coefficient bound. -/
theorem three_pow_div_two_pow_le_exp_log_two_mul_mul_three_four_pow
    {q w : ℕ} {H : ℝ}
    (hw : 2 * (q : ℝ) - H ≤ (w : ℝ)) :
    (3 : ℝ) ^ q / (2 : ℝ) ^ w ≤
      Real.exp (Real.log 2 * H) * (3 / 4 : ℝ) ^ q := by
  have hmul :=
    mul_le_mul_of_nonneg_right hw log_two_pos_coefficient.le
  rw [three_pow_div_two_pow_eq_exp, three_four_pow_eq_exp,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [log_three_four_eq]
  nlinarith

end Tao
end Erdos1135
