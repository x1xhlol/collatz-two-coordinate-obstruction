/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.CountableMarkov
import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

def geom2PNatListTerminalValue (as : List ℕ+) : ℕ :=
  match as.getLast? with
  | none => 0
  | some a => (a : ℕ)

theorem geom2PNatListTerminalValue_eq_getLast
    {as : List ℕ+} (has : as ≠ []) :
    geom2PNatListTerminalValue as = (as.getLast has : ℕ) := by
  simp [geom2PNatListTerminalValue,
    List.getLast?_eq_getLast_of_ne_nil has]

end

end Tao

end Erdos1135Predecessor
