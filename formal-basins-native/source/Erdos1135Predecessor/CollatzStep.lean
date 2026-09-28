/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Basic

namespace Erdos1135Predecessor

lemma collatzStep_eq_div_two_of_even {n : ℕ} (hn : Even n) :
    collatzStep n = n / 2 := by
  simp [collatzStep, CollatzConjecturePredecessor.collatzStep, hn]

lemma collatzStep_eq_three_mul_add_one_of_not_even {n : ℕ} (hn : ¬ Even n) :
    collatzStep n = 3 * n + 1 := by
  simp [collatzStep, CollatzConjecturePredecessor.collatzStep, hn]

end Erdos1135Predecessor
