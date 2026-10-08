/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7Geometry
import Erdos1135Predecessor.Tao.Probability.Finite
import Erdos1135Predecessor.Tao.Renewal.Lemma710EprimeProbability
import Erdos1135Predecessor.Tao.Renewal.Lemma710KernelWindow
import Erdos1135Predecessor.Tao.Renewal.Lemma710PostStoppedKernel
import Erdos1135Predecessor.Tao.Renewal.Lemma77PotentialCore
import Erdos1135Predecessor.Tao.Section6.Corollary63

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

def relativeVerticalOvershoot (s : ℕ) (ell : ℤ) : ℤ :=
  ell - (s : ℤ)

theorem relativeVerticalOvershoot_pos_of_lt
    {s : ℕ} {ell : ℤ} (hlt : (s : ℤ) < ell) :
    0 < relativeVerticalOvershoot s ell := by
  exact sub_pos.mpr hlt

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
