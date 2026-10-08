/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitLogarithmicConductorRoom
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitPositiveDensityPair
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitSeedToCount
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem explicitLogarithmicRoomStart_mono : Monotone explicitLogarithmicRoomStart := by
  intro m k hmk
  unfold explicitLogarithmicRoomStart
  exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.clog_mono_right 2 hmk) 78)

end

end Erdos1135Predecessor.ND.PositiveDensity
