/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma710PostStoppedKernel

namespace Erdos1135Predecessor

namespace Tao

namespace TaoSection7Lemma710

def EprimeSourceEvent
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold horizontalSourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  EprimeVerticalSourceEvent start old verticalSourceThreshold full ∨
    EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full

end TaoSection7Lemma710

end Tao

end Erdos1135Predecessor
