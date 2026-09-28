/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageExpMoment
import Erdos1135Predecessor.Tao.Renewal.Lemma79CanonicalExitWhite
import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstEntryFiberLaw
import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstExit
import Erdos1135Predecessor.Tao.Renewal.Lemma79R2Aggregation
import Erdos1135Predecessor.Tao.Renewal.Lemma79R2EndpointContraction
import Erdos1135Predecessor.Tao.Renewal.Lemma79R2MasterTransport
import Erdos1135Predecessor.Tao.Renewal.Lemma79R2PositiveKey

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79PMFENNExpectation_indicator_eq_zero_of_mass_eq_zero
    {Omega : Type*} (mu : PMF Omega) (Event : Set Omega)
    (F : Omega -> ENNReal)
    (hmass : mu.toOuterMeasure Event = 0) :
    lemma79PMFENNExpectation mu (Event.indicator F) = 0 := by
  have hdisjoint : Disjoint mu.support Event :=
    (PMF.toOuterMeasure_apply_eq_zero_iff mu Event).1 hmass
  unfold lemma79PMFENNExpectation
  rw [ENNReal.tsum_eq_zero]
  intro omega
  by_cases hEvent : omega ∈ Event
  · have hmu : mu omega = 0 := by
      by_contra hne
      exact (Set.disjoint_left.1 hdisjoint) hne hEvent
    simp [hmu]
  · simp [Set.indicator, hEvent]

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
