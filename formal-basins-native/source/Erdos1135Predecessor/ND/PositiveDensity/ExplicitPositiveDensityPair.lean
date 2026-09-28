/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitSeedToCount
import Mathlib.Data.Nat.Sqrt

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitDensityFloor : ℕ := 2 ^ 80

end

end Erdos1135Predecessor.ND.PositiveDensity
