import Erdos1135.ND.Band.A5PhysicalPaddingRate
import Erdos1135.ND.Band.A5PrefixGood
import Erdos1135.Tao.Section5.PassLostWindow

/-!
# A5 Full-Good Ingress to the Tao EPrime Endpoint Set

This endpoint-shaped leaf combines the literal frozen-v10 full-prefix Good
event with Tao's checked lost-window theorem.  The deterministic core keeps
the three exact guards visible: passage after `m0`, passage before `n0`, and
the physical-width comparison with Tao's source-typicality slack.
-/

namespace Erdos1135
namespace ND

open Filter

noncomputable section

/-- A full-prefix Good passage event localizes its common step-back endpoint
inside Tao's full `EPrime` set. -/
theorem ndA5PassEventAtTime_shifted_mem_EPrime_of_fullPrefixGood
    {B n : ℕ} {C : ℝ} {N : Tao.TaoOddNat} {E : Set ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hm : Tao.taoSection5M0 B ≤ n)
    (hn0 : n ≤ Tao.taoSection5N0 B)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hpass : Tao.taoSection5PassEventAtTime B N.1 n E) :
    (Tao.syracuse^[n - Tao.taoSection5M0 B]) N.1 ∈
      Tao.taoSection5EPrime B E := by
  exact Tao.taoSection5PassEvent_shifted_mem_EPrime lost N.2 hm
    (Tao.TaoSection5SourceTypicalTuple.to_closed
      (ndA5FullPrefixGoodEvent_sourceTypicalPrefix hwidth hgood hn0))
    hpass

/-- The `(t2)` scale packet supplies both time guards required by the
full-prefix Good ingress. -/
theorem ndA5T2PassEventAtTime_shifted_mem_EPrime_of_fullPrefixGood
    {B n : ℕ} {C : ℝ} {N : Tao.TaoOddNat} {E : Set ℕ}
    (lost : Tao.TaoSection5PassLostWindowFacts B)
    (hB : 1 ≤ B)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hpass : Tao.taoSection5PassEventAtTime B N.1 n E) :
    (Tao.syracuse^[n - Tao.taoSection5M0 B]) N.1 ∈
      Tao.taoSection5EPrime B E :=
  ndA5PassEventAtTime_shifted_mem_EPrime_of_fullPrefixGood
    lost ht2.m0_le (ht2.le_n0 hB) hwidth hgood hpass

/-- At every sufficiently large source scale, a fixed positive physical tube
and a `(t2)` passage packet feed the checked Tao `EPrime` endpoint theorem. -/
theorem eventually_ndA5T2PassEventAtTime_shifted_mem_EPrime_of_fullPrefixGood
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in atTop,
      ∀ {n : ℕ} {N : Tao.TaoOddNat} {E : Set ℕ},
        NDA5T2ScaleFacts B n C →
        N ∈ ndA5FullPrefixGoodEvent B C →
        Tao.taoSection5PassEventAtTime B N.1 n E →
        (Tao.syracuse^[n - Tao.taoSection5M0 B]) N.1 ∈
          Tao.taoSection5EPrime B E := by
  filter_upwards [Tao.eventually_taoSection5PassLostWindowFacts,
    eventually_ndA5TubeWidth_le_taoSection5TypicalSlack C hC,
    eventually_ge_atTop (1 : ℕ)] with B lost hwidth hB
  intro n N E ht2 hgood hpass
  exact ndA5T2PassEventAtTime_shifted_mem_EPrime_of_fullPrefixGood
    lost hB ht2 hwidth hgood hpass

end

end ND
end Erdos1135
