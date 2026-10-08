/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

theorem pmf_sum_toReal {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a, (p a).toReal) = 1 := by
  have htsum := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [ENNReal.tsum_toReal_eq (PMF.apply_ne_top p)] at htsum
  rw [tsum_fintype] at htsum
  simpa using htsum

end Tao

end Erdos1135Predecessor
