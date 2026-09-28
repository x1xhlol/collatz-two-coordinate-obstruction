/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.GatedSubmass
import Erdos1135Predecessor.Tao.Section6.HeadGateLocalization
import Erdos1135Predecessor.Tao.Syracuse.ValuationDistribution

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection6HeadOptionPMF
    (CA : ℝ) (n k l : ℕ) : PMF (Option (ZMod (3 ^ n))) :=
  taoGatedOptionPMF
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)

noncomputable def taoSection6HeadSubmass
    (CA : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  taoGatedSubmass
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)
    y

theorem geom2PNatListPMF_apply_toReal_eq_headGate_weight
    {CA : ℝ} {n k l : ℕ} {head : List ℕ+}
    (hgate : taoSection6HeadGate CA n k l head) :
    (geom2PNatListPMF (k + 1) head).toReal = (1 / 2 : ℝ) ^ l := by
  rw [← taoSection6HeadGate_length hgate]
  rw [geom2PNatListPMF_apply_length_toReal_eq_weight]
  rw [taoSection6HeadGate_weight hgate]

theorem taoSection6HeadSubmass_eq_zero_of_headGate_empty
    {CA : ℝ} {n k l : ℕ}
    (hempty : ¬ ∃ head : List ℕ+,
      taoSection6HeadGate CA n k l head)
    (y : ZMod (3 ^ n)) :
    taoSection6HeadSubmass CA n k l y = 0 := by
  unfold taoSection6HeadSubmass
  exact taoGatedSubmass_eq_zero_of_not_exists_gate
    (geom2PNatListPMF (k + 1))
    (taoSection6HeadGate CA n k l)
    (taoCor63SourceOffsetZMod n l)
    hempty y

end

end Tao

end Erdos1135Predecessor
