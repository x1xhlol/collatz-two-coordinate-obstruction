/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeSourceWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open Filter Topology

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79OutsideEprimeErrorMargin_of_split_absorption
    {Aweight p : ℕ} {S : ℝ}
    (hJ :
      2 * S ^ (3 / 5 : ℝ) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) / 2)
    (hL :
      (Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1 ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) / 2) :
    2 * S ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
      S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  linarith

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
