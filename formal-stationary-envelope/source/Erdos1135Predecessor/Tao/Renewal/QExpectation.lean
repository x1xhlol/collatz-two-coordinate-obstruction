/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldExpectation
import Erdos1135Predecessor.Tao.Renewal.HoldIID
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

def TaoSection7QBounded01
    (Q : TaoSection7RenewalPoint → ℝ) : Prop :=
  ∀ p, 0 ≤ Q p ∧ Q p ≤ 1

noncomputable def taoSection7FullHoldQRecursionRHS
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (Q : TaoSection7RenewalPoint → ℝ)
    (p : TaoSection7RenewalPoint) : ℝ :=
  taoSection7QWhiteFactor epsilon W p *
    taoSection7HoldExpectationFull (fun h => Q (p + h))

end Tao

end Erdos1135Predecessor
