/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Geom2ListProjectivity
import Erdos1135Predecessor.Tao.Syracuse.AffineReverse

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem geom2PNatListMass_reverse (as : List ℕ+) :
    geom2PNatListMass as.reverse = geom2PNatListMass as := by
  simp only [geom2PNatListMass_eq_inv_pow, taoTupleWeight_reverse]

theorem geom2PNatListPMF_apply_reverse (n : ℕ) (as : List ℕ+) :
    geom2PNatListPMF n as.reverse = geom2PNatListPMF n as := by
  by_cases hlen : as.length = n
  · apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top (geom2PNatListPMF n) as.reverse)
      (PMF.apply_ne_top (geom2PNatListPMF n) as)).mp
    have hlenr : as.reverse.length = n := by simpa using hlen
    calc
      (geom2PNatListPMF n as.reverse).toReal =
          geom2PNatListMass as.reverse := by
        simpa only [hlenr] using
          geom2PNatListPMF_apply_length_toReal as.reverse
      _ = geom2PNatListMass as := geom2PNatListMass_reverse as
      _ = (geom2PNatListPMF n as).toReal := by
        simpa only [hlen] using
          (geom2PNatListPMF_apply_length_toReal as).symm
  · have hlenr : as.reverse.length ≠ n := by simpa using hlen
    rw [geom2PNatListPMF_apply_eq_zero_of_length_ne n as.reverse hlenr,
      geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlen]

end

end Tao

end Erdos1135Predecessor
