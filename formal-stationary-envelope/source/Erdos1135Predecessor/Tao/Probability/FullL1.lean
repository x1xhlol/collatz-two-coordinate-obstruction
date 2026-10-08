/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

theorem taoPMF_summable_toReal {α : Type*} (p : PMF α) :
    Summable fun a : α => (p a).toReal := by
  refine ENNReal.summable_toReal ?_
  rw [PMF.tsum_coe p]
  norm_num

theorem pmfOuterMass_toReal_eq_tsum_indicator
    {α : Type*} (p : PMF α) (E : Set α) :
    (p.toOuterMeasure E).toReal =
      ∑' a : α, E.indicator (fun a => (p a).toReal) a := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : a ∈ E <;> simp [Set.indicator, h]
  · intro a
    by_cases h : a ∈ E <;>
      simp [Set.indicator, h, PMF.apply_ne_top p a]

end Tao

end Erdos1135Predecessor
