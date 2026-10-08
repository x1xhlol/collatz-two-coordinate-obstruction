/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78ActiveCover
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Stopping
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOuterBadJ
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79_exists_qmBoundaryFarBelow_entryTriangle_gap_bounds
    {n m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hactive : TaoSection7Prop78ActiveCoverData n xi epsilon)
    {entry : TaoSection7RenewalPoint}
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hfar :
      TaoSection7QmBoundaryFarBelow
        (taoSection7Prop78BoundaryThreshold m)
        hactive.family entry) :
    ∃ Delta ∈ hactive.family,
      Delta.Mem entry.toPoint ∧
      taoSection7Prop78BoundaryThreshold m <
        (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ∧
      (lemma79EntryVerticalGap Delta entry.toPoint : ℝ) ≤
        (Real.log 9 / Real.log 2) * (m : ℝ) := by
  rcases hfar with ⟨Delta, hDelta, hmem, hfarDepth⟩
  have hdomain :=
    taoSection7QmBoundary_toPoint_sourceDomain hboundary
  have hright :
      TaoSection7TriangleRightEdgeInStrip ((n / 2 : ℕ) : ℝ) Delta :=
    hactive.rightEdge hDelta
  have hupper :=
    taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_domain
      hmem hdomain hright
  have hsub : n / 2 - (entry.j : ℕ) = m := by
    unfold taoSection7QmBoundary at hboundary
    omega
  have hcurrent :
      taoSection7Lemma710CurrentM n entry.toPoint = (m : ℝ) := by
    unfold taoSection7Lemma710CurrentM
    simpa [TaoSection7RenewalPoint.toPoint] using
      congrArg (fun k : ℕ => (k : ℝ)) hsub
  have hgap :
      Delta.verticalDepth entry.toPoint =
        (lemma79EntryVerticalGap Delta entry.toPoint : ℤ) := by
    simpa [TaoSection7Triangle.verticalDepth] using
      lemma79EntryVerticalGap_coe_of_mem hmem
  refine ⟨Delta, hDelta, hmem, ?_, ?_⟩
  · simpa [hgap] using hfarDepth
  · simpa [hgap, hcurrent] using hupper

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
