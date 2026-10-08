/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Statement

/-!
# Threshold Lower Bounds To Tao Almost-Bounded Assembly

This module proves the statement-level consumer from finite-threshold
logarithmic lower bounds to the existing almost-bounded Collatz statement
surface.  It does not prove the analytic finite-threshold lower bounds.
-/

namespace Erdos1135SecondScale
namespace Tao

open Filter
open scoped Topology

theorem taoAlmostBounded_of_thresholdLowerBound {eps : ℕ → ℝ}
    (heps : ThresholdLowerBoundHypothesis eps) :
    TaoAlmostBoundedStatement := by
  intro f hf
  let S : Set ℕ := {N : ℕ | 0 < N ∧ collatzHitsBelowReal N (f N)}
  refine HasLogDensity.of_eventually_superset_of_lower_tendsto_one
    (A := fun k : ℕ => collatzThresholdGood (k + 2))
    (S := S)
    (d := fun k : ℕ => 1 - eps (k + 2)) ?hsub ?hlower ?hd
  · intro k
    simpa [S] using
      (eventually_thresholdGood_subset_hitsBelowReal (f := f) hf (B := k + 2))
  · intro k
    exact heps.2 (k + 2) (Nat.le_add_left 2 k)
  · have heps_shift :
        Tendsto (fun k : ℕ => eps (k + 2)) atTop (nhds 0) :=
      heps.1.comp (Filter.tendsto_add_atTop_nat 2)
    simpa using heps_shift.const_sub (1 : ℝ)

theorem taoThresholdAssemblyStatement :
    TaoThresholdAssemblyStatement := by
  intro eps heps
  exact taoAlmostBounded_of_thresholdLowerBound heps

end Tao
end Erdos1135SecondScale
