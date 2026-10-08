/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QExpectation
import Erdos1135SecondScale.Tao.Renewal.QFiniteApprox

/-!
# Section 7 Actual Q Recursion Combiner

This module proves Tao's full-Hold recursion `(7.35)` for a supplied actual
`Q` already identified as the pointwise finite limit of the terminal-one
finite approximants.  It does not construct that limit or instantiate the
source cutoff `Q`.
-/

open scoped BigOperators Topology

namespace Erdos1135SecondScale
namespace Tao

theorem taoSection7ActualQ_fullHoldQRecursion_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (p : TaoSection7RenewalPoint) :
    Q p = taoSection7FullHoldQRecursionRHS epsilon W Q p := by
  let A : ℕ → TaoSection7RenewalPoint → ℝ :=
    fun K q => taoSection7QFiniteTerminalOneApprox K epsilon W q
  have hshift :
      Filter.Tendsto (fun K : ℕ => A (K + 1) p)
        Filter.atTop (𝓝 (Q p)) := by
    exact (hQ p).comp (Filter.tendsto_add_atTop_nat 1)
  have hleft :
      Filter.Tendsto
        (fun K : ℕ =>
          taoSection7QWhiteFactor epsilon W p *
            taoSection7HoldExpectationFull (fun h => A K (p + h)))
        Filter.atTop (𝓝 (Q p)) := by
    refine hshift.congr' ?_
    exact Filter.Eventually.of_forall fun K => by
      dsimp [A]
      exact taoSection7QFiniteTerminalOneApprox_succ hepsilon K W p
  have hexp :
      Filter.Tendsto
        (fun K : ℕ =>
          taoSection7HoldExpectationFull (fun h => A K (p + h)))
        Filter.atTop
        (𝓝 (taoSection7HoldExpectationFull (fun h => Q (p + h)))) := by
    refine taoSection7HoldExpectationFull_tendsto_of_bounded01 ?_ ?_ ?_
    · intro h
      exact hQ (p + h)
    · intro K h
      exact taoSection7QFiniteTerminalOneApprox_nonneg K epsilon W (p + h)
    · intro K h
      exact taoSection7QFiniteTerminalOneApprox_le_one (K := K) hepsilon W (p + h)
  have hright :
      Filter.Tendsto
        (fun K : ℕ =>
          taoSection7QWhiteFactor epsilon W p *
            taoSection7HoldExpectationFull (fun h => A K (p + h)))
        Filter.atTop
        (𝓝 (taoSection7FullHoldQRecursionRHS epsilon W Q p)) := by
    unfold taoSection7FullHoldQRecursionRHS
    exact tendsto_const_nhds.mul hexp
  exact tendsto_nhds_unique hleft hright

end Tao
end Erdos1135SecondScale
