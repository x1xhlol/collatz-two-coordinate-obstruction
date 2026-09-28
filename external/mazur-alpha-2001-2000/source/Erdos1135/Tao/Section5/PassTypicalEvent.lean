import Erdos1135.Tao.Section5.PassSchedule
import Erdos1135.Tao.Syracuse.OddSource

/-!
# Section 5 Typical Source Events

This dependency-light leaf owns the strict and closed full-prefix events used
by both deterministic and probabilistic Section 5 consumers.  It contains no
passage-event, affine, Proposition 1.9, or concentration argument.
-/

namespace Erdos1135
namespace Tao

/-- Full closed typicality through the common horizon `n0`. -/
def taoSection5ClosedGoodEvent (B : ℕ) : Set TaoOddNat :=
  {N | taoSection5TypicalTuple B (taoSection5N0 B)
    (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2)}

/-- Tao's strict source-facing typicality event through the common horizon. -/
def taoSection5SourceTypicalEvent (B : ℕ) : Set TaoOddNat :=
  {N | taoSection5SourceTypicalTuple B (taoSection5N0 B)
    (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2)}

theorem taoSection5SourceTypicalEvent_subset_closedGoodEvent (B : ℕ) :
    taoSection5SourceTypicalEvent B ⊆ taoSection5ClosedGoodEvent B := by
  intro N hN
  exact TaoSection5SourceTypicalTuple.to_closed hN

end Tao
end Erdos1135
