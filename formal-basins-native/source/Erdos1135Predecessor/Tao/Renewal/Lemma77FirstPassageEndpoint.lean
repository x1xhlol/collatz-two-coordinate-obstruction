/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldStoppedTail
import Erdos1135Predecessor.Tao.Renewal.Lemma77HorizontalMarginal

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

def lemma77CenteredHorizontalDisplacement (s r : ℕ) : ℝ :=
  (r : ℝ) - (s : ℝ) / 4

def lemma77PointwiseEndpointKernel
    (A B C D : ℝ) (s r : ℕ) (overshoot : ℤ) : ℝ :=
  C * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (Real.exp
        (-A * ((lemma77CenteredHorizontalDisplacement s r) ^ 2 /
          (1 + (s : ℝ)))) +
      Real.exp (-B * |lemma77CenteredHorizontalDisplacement s r|)) *
    Real.exp (-D * (overshoot : ℝ))

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
