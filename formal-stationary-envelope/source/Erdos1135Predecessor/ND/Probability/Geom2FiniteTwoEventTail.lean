/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.FullL1
import Erdos1135Predecessor.Tao.Probability.Geom2CenteredMoment
import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity

namespace Erdos1135Predecessor

namespace ND

open scoped BigOperators

noncomputable section

theorem geom2PNatListPMF_take_event_outerMeasure_toReal
    {r m : ℕ} (hrm : r ≤ m) (A : Set (List ℕ+)) :
    ((Tao.geom2PNatListPMF m).toOuterMeasure
      ((fun bs => bs.take r) ⁻¹' A)).toReal =
    ((Tao.geom2PNatListPMF r).toOuterMeasure A).toReal := by
  rw [← Tao.geom2PNatListPMF_map_take_low_eq_of_le hrm]
  rw [PMF.toOuterMeasure_map_apply]

end

end ND

end Erdos1135Predecessor
