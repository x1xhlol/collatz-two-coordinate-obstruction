/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.CanonicalFirstPassageEndpoint

/-!
# Lemma 7.9 Endpoint/Fresh Coordinates

Deterministic coordinate identities for restarting a fresh Hold path from a
relative canonical endpoint.  These identities do not depend on PMF support.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Advancing `P` fresh Hold increments from a relative endpoint is the
corresponding relative endpoint with both fresh prefix increments added. -/
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
end Erdos1135SecondScale
