/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135Predecessor.Tao.Renewal.HoldListVerticalTail
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3BaseKcutFiniteSum
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarEprime
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEStarMass
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeHorizontalTail
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeMarginalMass
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshEprimeMasterWidth
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshOutsideEprimeNative

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

theorem TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.sum_canonicalTerms_le
    {allowed : Finset ℕ}
    {Aweight base Kcut : ℕ}
    {constants : TaoSection7Lemma710Constants}
    (h :
      TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
        allowed Aweight base Kcut constants) :
    allowed.sum
        (fun p =>
          taoSection7Case3BaseKcutPolynomialBudgetTerm
              constants Aweight base Kcut p +
            taoSection7Case3BaseKcutExponentialBudgetTerm
              constants Aweight p) ≤
      (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) := by
  rw [Finset.sum_add_distrib]
  exact
    (add_le_add h.polynomial_sum_le h.exponential_sum_le).trans
      h.scalar_tail_budget

open TaoSection7Lemma77

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

theorem lemma79FixedOffsetBudget_eq_baseKcutTerms
    (constants : TaoSection7Lemma710Constants)
    (Aweight base Kcut p : ℕ) :
    constants.C710 * lemma79OutsideEprimeScale Aweight p /
          taoSection7Case3LargeTriangleBoundWithBase
            (base : ℝ) Kcut p +
        constants.C710 * Real.exp
          (-(constants.c710 * lemma79OutsideEprimeScale Aweight p)) =
      taoSection7Case3BaseKcutPolynomialBudgetTerm
          constants Aweight base Kcut p +
        taoSection7Case3BaseKcutExponentialBudgetTerm
          constants Aweight p := by
  simp only [lemma79OutsideEprimeScale,
    lemma79OutsideEprimeScaleNat,
    taoSection7Case3BaseKcutPolynomialBudgetTerm,
    taoSection7Case3BaseKcutExponentialBudgetTerm]
  push_cast
  ring_nf

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
