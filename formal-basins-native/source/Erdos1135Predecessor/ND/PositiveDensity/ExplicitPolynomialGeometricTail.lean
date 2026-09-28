/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem polynomialGeometric_moment_le (d : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * r ^ n) ∧
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ d * r ^ n) ≤
        (d.factorial : ℝ) / (1 - r) ^ (d + 1) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hbound (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) ^ d * r ^ n ≤
        (d.factorial : ℝ) * ((n + d).choose d : ℝ) * r ^ n := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
    exact_mod_cast (show (n + 1) ^ d ≤ d.factorial * (n + d).choose d by
      rw [← Nat.ascFactorial_eq_factorial_mul_choose]
      exact Nat.pow_succ_le_ascFactorial (n + 1) d)
  have hs := (summable_choose_mul_geometric_of_norm_lt_one d hr).mul_left
    (d.factorial : ℝ)
  have hf : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * r ^ n) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbound
      (by simpa only [mul_assoc] using hs)
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (d.factorial : ℝ) * (((n + d).choose d : ℝ) * r ^ n) :=
      hf.tsum_le_tsum (fun n => by simpa only [mul_assoc] using hbound n) hs
    _ = _ := by rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one d hr]; ring

end

end Erdos1135Predecessor.ND.PositiveDensity
