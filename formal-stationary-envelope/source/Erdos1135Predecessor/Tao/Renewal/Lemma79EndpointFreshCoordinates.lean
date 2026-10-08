/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageEndpoint

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79EndpointFresh_pathPoint_eq_relativeEndpoint
    (entry : TaoSection7RenewalPoint) (endpoint : ℕ × ℤ)
    (fresh : List TaoSection7RenewalPoint) (P : ℕ) :
    taoSection7RenewalPathPoint
        (lemma77RenewalPointOfRelativeEndpoint entry endpoint) fresh P =
      lemma77RenewalPointOfRelativeEndpoint entry
        (endpoint.1 + lemma77HoldPrefixHorizontalDelta P fresh,
          endpoint.2 + lemma77HoldPrefixVerticalIncrement entry P fresh) := by
  let origin := lemma77RenewalPointOfRelativeEndpoint entry endpoint
  have hvertical :
      lemma77HoldPrefixVerticalIncrement origin P fresh =
        lemma77HoldPrefixVerticalIncrement entry P fresh :=
    lemma77HoldPrefixVerticalIncrement_start_eq origin entry P fresh
  have hpath_l :
      (taoSection7RenewalPathPoint origin fresh P).l =
        origin.l + lemma77HoldPrefixVerticalIncrement origin P fresh := by
    change (taoSection7RenewalPathPoint origin fresh P).l =
      origin.l +
        ((taoSection7RenewalPathPoint origin fresh P).l - origin.l)
    omega
  change taoSection7RenewalPathPoint origin fresh P = _
  ext
  · apply PNat.eq
    rw [lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]
    simp only [origin, lemma77RenewalPointOfRelativeEndpoint_j]
    omega
  · rw [hpath_l, hvertical]
    simp only [origin, lemma77RenewalPointOfRelativeEndpoint_l]
    omega

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
