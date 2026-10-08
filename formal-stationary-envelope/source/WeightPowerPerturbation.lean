import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CollatzCanonical.WeightPerturbation

/-- The sharp universal upper bound follows from the tangent inequality for the exponential. -/
theorem neg_mul_log_le_inv_exp {w : ℝ} (hw : 0 < w) :
    -w * Real.log w ≤ (Real.exp 1)⁻¹ := by
  have h := Real.add_one_le_exp (-1 - Real.log w)
  rw [Real.exp_sub, Real.exp_neg, Real.exp_log hw] at h
  have hlog : -Real.log w ≤ (Real.exp 1)⁻¹ / w := by linarith
  have hm := (le_div_iff₀ hw).mp hlog
  nlinarith

/-- A uniform estimate for replacing a weight by a nearby larger power. -/
theorem uniform_weight_power_perturbation {w ε : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hε : 0 ≤ ε) :
    0 ≤ w - w ^ (1 + ε) ∧ w - w ^ (1 + ε) ≤ ε / Real.exp 1 := by
  refine ⟨sub_nonneg.mpr (Real.rpow_le_self_of_le_one hw0 hw1 (by linarith)), ?_⟩
  by_cases hwz : w = 0
  · subst w
    rw [Real.zero_rpow (show (1 : ℝ) + ε ≠ 0 by linarith)]
    simp only [sub_self]
    positivity
  · have hw : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hwz)
    have hpow : w ^ (1 + ε) = w * Real.exp (Real.log w * ε) := by
      rw [Real.rpow_add hw, Real.rpow_one, Real.rpow_def_of_pos hw]
    have ht := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (Real.log w * ε)) hw0
    have hdiff : w - w ^ (1 + ε) ≤ ε * (-w * Real.log w) := by
      rw [hpow]
      nlinarith
    calc
      w - w ^ (1 + ε) ≤ ε * (-w * Real.log w) := hdiff
      _ ≤ ε * (Real.exp 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (neg_mul_log_le_inv_exp hw) hε
      _ = ε / Real.exp 1 := by rw [div_eq_mul_inv]

theorem abs_weight_power_perturbation {w ε : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hε : 0 ≤ ε) :
    |w - w ^ (1 + ε)| ≤ ε / Real.exp 1 := by
  obtain ⟨hl, hu⟩ := uniform_weight_power_perturbation hw0 hw1 hε
  simpa only [abs_of_nonneg hl] using hu

#print axioms neg_mul_log_le_inv_exp
#print axioms uniform_weight_power_perturbation
#print axioms abs_weight_power_perturbation

end CollatzCanonical.WeightPerturbation
