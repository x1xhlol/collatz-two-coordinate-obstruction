/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Syracuse.Affine
import Erdos1135Predecessor.Terras.Core.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

namespace Erdos1135Predecessor

namespace Tao

theorem syracuse_iterate_odd (n N : ℕ) (hN : Odd N) :
    Odd ((syracuse^[n]) N) := by
  induction n generalizing N with
  | zero =>
      simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syracuse N) (syracuse_odd N)

end Tao

end Erdos1135Predecessor
