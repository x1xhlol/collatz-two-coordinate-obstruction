/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Prop78ActiveCover
import Erdos1135SecondScale.Tao.Renewal.Prop78Case3Stopping

/-!
# Section 7 Case 3 Active-Cover Stopping Compatibility

This thin integration module routes active-cover disjointness into the Case 3
one-step stopping packet.  It does not prove the actual finite
`steps.take R = constructed_prefix` bridge, source-derived indexed recurrence,
Lemma 7.9, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135SecondScale
namespace Tao

/--
Compare two initial stopping pairs using the pairwise-disjoint triangle family
from the active-cover socket.

This is the head-initial analogue of the one-step transition compatibility
below; the finite take-prefix equality still requires an induction over the
actual stopping prefix.
-/
theorem taoSection7Case3_initialPair_eq_of_activeCover_initialStoppingStep
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {pointAt : ℕ → TaoSection7Point}
    {first first' : ℕ}
    {Γ Γ' : TaoSection7Triangle}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    (hinit :
      TaoSection7Case3InitialStoppingStep
        pointAt hactive.family first Γ)
    (hinit' :
      TaoSection7Case3InitialStoppingStep
        pointAt hactive.family first' Γ') :
    (first, Γ) = (first', Γ') :=
  hinit.pair_eq_of_pairwiseDisjoint hactive.pairwiseDisjoint hinit'

/--
Compare an actual stopping-transition head with a produced one-step packet
using the pairwise-disjoint triangle family from the active-cover socket.

This is a head-compatibility adapter only.  The finite induction proving that
the constructed prefix is the first `R` steps of the terminal actual run
remains a separate producer.
-/
theorem taoSection7Case3_oneStepPair_eq_of_activeCover_stoppingTransition
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := hactive.family)
        (pointAt := pointAt) (Accepts := Accepts) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old)
    (hstep :
      TaoSection7Case3StoppingTransition
        pointAt hactive.family q old first Γ) :
    (first, Γ) = (hupdate.first, hupdate.triangle) :=
  hupdate.pair_eq_of_pairwiseDisjoint_stoppingTransition
    hactive.pairwiseDisjoint hstep

end Tao
end Erdos1135SecondScale
