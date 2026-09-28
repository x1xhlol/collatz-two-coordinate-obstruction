/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.CollatzStep
import Erdos1135Predecessor.Tao.Syracuse.Basic

namespace Erdos1135Predecessor

namespace Tao

theorem collatz_iterate_powTwo_mul (a M : ℕ) :
    (collatzStep^[a]) ((2 : ℕ) ^ a * M) = M := by
  induction a with
  | zero =>
      simp
  | succ a ih =>
      have hEven : Even ((2 : ℕ) ^ (a + 1) * M) := by
        refine ⟨(2 : ℕ) ^ a * M, ?_⟩
        rw [pow_succ]
        ring
      rw [Function.iterate_succ_apply,
        collatzStep_eq_div_two_of_even hEven]
      have hdiv :
          ((2 : ℕ) ^ (a + 1) * M) / 2 = (2 : ℕ) ^ a * M := by
        rw [pow_succ]
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_div_left ((2 : ℕ) ^ a * M) (by norm_num : 0 < (2 : ℕ))
      rw [hdiv]
      exact ih

theorem collatz_iterate_syracuse_block {M : ℕ} (hM : Odd M) :
    (collatzStep^[syracuseExponent M + 1]) M = syracuse M := by
  rw [Function.iterate_add_apply, Function.iterate_one,
    collatzStep_eq_three_mul_add_one_of_not_even
      (Nat.not_even_iff_odd.mpr hM),
    ← two_pow_syracuseExponent_mul_syracuse M]
  exact collatz_iterate_powTwo_mul (syracuseExponent M) (syracuse M)

end Tao

end Erdos1135Predecessor
