/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricBalancedCrossingAffineDensity
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricFirstCrossingOvershootRate
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricOutwardBaseGrowth

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

universe u

structure NDGeom2ShiftedWideSymmetricRegenerativeState where
  Label : Type u
  [labelFintype : Fintype Label]
  root : Label → ℕ
  base : Label → ℕ
  outerWeight : Label → ℝ
  weight_nonneg : ∀ i, 0 ≤ outerWeight i
  root_odd : ∀ i, Odd (root i)
  base_eq : ∀ i, base i = ndA5QOneRootDyadicBase (root i)
  base_twoHundred : ∀ i, 200 ≤ base i

theorem NDGeom2ShiftedWideSymmetricRegenerativeState.rootLower
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState)
    (i : S.Label) :
    16 ^ S.base i ≤ S.root i := by
  rw [S.base_eq i]
  exact (rootDyadicBase_bounds (Odd.pos (S.root_odd i))).1

noncomputable def NDGeom2ShiftedWideSymmetricRegenerativeState.denominator
    (S : NDGeom2ShiftedWideSymmetricRegenerativeState) : ℝ := by
  letI := S.labelFintype
  exact ndGeom2PredictableOuterDenominator
    (Finset.univ : Finset S.Label) S.outerWeight

end

end PositiveDensity

end ND

end Erdos1135Predecessor
