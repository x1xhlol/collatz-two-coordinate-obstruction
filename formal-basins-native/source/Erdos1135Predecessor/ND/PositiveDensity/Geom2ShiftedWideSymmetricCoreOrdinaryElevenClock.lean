/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricWholeHistoryOrdinaryClock

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullClockFloorSum_eq_coreBaseSum_add_terminalFloor
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    U.fullClockFloorSum cap n = U.coreBaseSum cap n + (U.forwardIterate cap n).floor := by
  induction n generalizing U cap with
  | zero => simp [fullClockFloorSum, coreBaseSum, forwardIterate]
  | succ n ih => simp only [fullClockFloorSum, coreBaseSum, forwardIterate, ih, Nat.add_assoc]

theorem fullTerminalPath_depth_eq_forward_length_add_terminal_depth
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    (U.fullTerminalPath cap n shift K z).depth =
      (U.forwardWord cap n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)).length +
        ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z := by
  rw [← (U.fullTerminalPath cap n shift K z).word_length,
    U.fullTerminalPath_word_eq_reverse, List.length_reverse]
  simp only [fullTerminalWord, List.length_append,
    ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length]

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
