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
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos1135Predecessor

namespace Terras

def twoAdicExponent (n : ℕ) : ℕ :=
  n.factorization 2

def oddOnly (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ twoAdicExponent (3 * n + 1)

end Terras

end Erdos1135Predecessor
