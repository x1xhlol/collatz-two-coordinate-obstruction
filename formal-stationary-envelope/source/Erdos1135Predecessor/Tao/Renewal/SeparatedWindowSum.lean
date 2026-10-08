/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

def taoSection7IntIccWindow (R : ℕ) (c : ℤ) : Finset ℤ :=
  Finset.Icc (c - (R : ℤ)) (c + (R : ℤ))

theorem mem_taoSection7IntIccWindow {R : ℕ} {c x : ℤ} :
    x ∈ taoSection7IntIccWindow R c ↔ c - (R : ℤ) ≤ x ∧ x ≤ c + (R : ℤ) := by
  simp [taoSection7IntIccWindow]

end

end Tao

end Erdos1135Predecessor
