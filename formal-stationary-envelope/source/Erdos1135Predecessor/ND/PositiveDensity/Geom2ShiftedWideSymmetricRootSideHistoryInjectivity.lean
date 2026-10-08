/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRegenerativeState
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideBoundedOvershootPhysicalIncidence

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

def ndGeom2RootSideCapTail (cap : ℕ → ℕ) : ℕ → ℕ :=
  fun n => cap (n + 1)

end

end PositiveDensity

end ND

end Erdos1135Predecessor
