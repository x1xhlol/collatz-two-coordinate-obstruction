import Erdos1135.Tao.Renewal.Prop78Case3BaseKcutFiniteSum
import Erdos1135.Tao.Renewal.QEndpointFreshEStarFixedOffset
import Erdos1135.Tao.Renewal.QEndpointFreshEStarMass

/-!
# Canonical Countable EStar Budget

This leaf sums the scheduled fixed-offset Lemma 7.10 bounds over the exact
inclusive survival envelope.  The scalar absorption uses no probability
carrier, and the event theorem stays on the canonical countable
endpoint/fresh law.

The survival-envelope union is sufficient for the stored stopping trace; it
is not asserted to equal Tao's larger printed union through every admissible
offset.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

/-- The separated polynomial and exponential row estimates imply the final
scalar budget directly, without passing through a finite probability-space
packet. -/
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

/-- The fixed-offset budget from the canonical probability theorem is
definitionally the sum of the existing base-`Kcut` scalar row terms. -/
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

/-- Carrier-free canonical PairEStar budget on the exact inclusive survival
range `0 ≤ p ≤ Pmax`.  The common cap hypothesis supplies `p ≤ J` for every
fixed-offset invocation, while the scalar absorption record closes the two
row sums. -/
theorem
    lemma79CanonicalEndpointFreshEStarEvent_toReal_le_baseKcutBudget :
    ∃ constants : TaoSection7Lemma710Constants,
      ∀ (Aweight base Kcut T R : ℕ), 8 ≤ Aweight →
        ∃ S0 : ℕ,
          ∀ (n m J fpGap : ℕ)
            (entry : TaoSection7RenewalPoint)
            (family : Set TaoSection7Triangle)
            (old : TaoSection7Triangle) (M : ℝ),
            S0 ≤ fpGap →
            lemma79CanonicalSurvivalMaxTime base Kcut T R ≤ J →
            old.cornerL - entry.l = (fpGap : ℤ) →
            old.Mem entry.toPoint →
            TaoSection7TriangleFamilyPairwiseDisjoint family →
            old ∈ family →
            TaoSection7Lemma710CurrentScaleControls
              n old entry.toPoint M (fpGap : ℝ) →
            2 ≤ m →
            M = (m : ℝ) →
            TaoSection7Case3BaseKcutAllowedCapAdmissibility
              (Finset.range
                (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1))
              base m Kcut
              (lemma79CanonicalSurvivalMaxTime base Kcut T R) →
            TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
              (Finset.range
                (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1))
              Aweight base Kcut constants →
            ((lemma79CanonicalEndpointFreshPMF J entry fpGap).toOuterMeasure
                (lemma79CanonicalEndpointFreshEStarEvent
                  entry family base Kcut T R)).toReal ≤
              (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) := by
  rcases
      lemma79CanonicalEndpointFreshEStarAt_outerMeasure_le_fixedOffset with
    ⟨constants, hfixed⟩
  refine ⟨constants, ?_⟩
  intro Aweight base Kcut T R hAweight
  rcases
      hfixed Aweight
        (lemma79CanonicalSurvivalMaxTime base Kcut T R) hAweight with
    ⟨S0, hfixedRows⟩
  refine ⟨S0, ?_⟩
  intro n m J fpGap entry family old M
    hS0 hPmaxJ hgap hbase hpair hold hscale hm hM hcap habsorb
  let allowed : Finset ℕ :=
    Finset.range (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1)
  let mu := lemma79CanonicalEndpointFreshPMF J entry fpGap
  have hbasePos : 0 < base := by
    exact lt_of_lt_of_le (by norm_num) habsorb.base_ge_four
  have hbaseReal : 0 < (base : ℝ) := by
    exact_mod_cast hbasePos
  have hpoly0 (p : ℕ) :
      0 ≤ taoSection7Case3BaseKcutPolynomialBudgetTerm
        constants Aweight base Kcut p := by
    unfold taoSection7Case3BaseKcutPolynomialBudgetTerm
    unfold taoSection7Case3LargeTriangleBoundWithBase
    exact mul_nonneg constants.C710_nonneg
      (div_nonneg
        (mul_nonneg (sq_nonneg _) (by positivity))
        (mul_nonneg
          (pow_nonneg hbaseReal.le _)
          (pow_nonneg (by positivity) _)))
  have hexp0 (p : ℕ) :
      0 ≤ taoSection7Case3BaseKcutExponentialBudgetTerm
        constants Aweight p := by
    unfold taoSection7Case3BaseKcutExponentialBudgetTerm
    exact mul_nonneg constants.C710_nonneg (Real.exp_pos _).le
  have hrow :
      ∀ p, p ∈ allowed →
        (mu.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarAt
            entry family base Kcut p)).toReal ≤
          taoSection7Case3BaseKcutPolynomialBudgetTerm
              constants Aweight base Kcut p +
            taoSection7Case3BaseKcutExponentialBudgetTerm
              constants Aweight p := by
    intro p hp
    have hpPmax :
        p ≤ lemma79CanonicalSurvivalMaxTime base Kcut T R := by
      have hpRange :
          p < lemma79CanonicalSurvivalMaxTime base Kcut T R + 1 := by
        simpa [allowed] using Finset.mem_range.1 hp
      omega
    have hpJ : p ≤ J := hpPmax.trans hPmaxJ
    have hbound :=
      hfixedRows
        (Finset.range
          (lemma79CanonicalSurvivalMaxTime base Kcut T R + 1))
        n m J fpGap base Kcut p entry family old M
        hS0 hpJ hgap hbase hpair hold hscale hm hM hcap
        (by simpa [allowed] using hp)
    have hfixedBudget0 :
        0 ≤ constants.C710 * lemma79OutsideEprimeScale Aweight p /
              taoSection7Case3LargeTriangleBoundWithBase
                (base : ℝ) Kcut p +
            constants.C710 * Real.exp
              (-(constants.c710 *
                lemma79OutsideEprimeScale Aweight p)) := by
      rw [lemma79FixedOffsetBudget_eq_baseKcutTerms]
      exact add_nonneg (hpoly0 p) (hexp0 p)
    have hreal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal hfixedBudget0] at hreal
    simpa [lemma79FixedOffsetBudget_eq_baseKcutTerms] using hreal
  calc
    (mu.toOuterMeasure
        (lemma79CanonicalEndpointFreshEStarEvent
          entry family base Kcut T R)).toReal ≤
      ∑ p ∈ allowed,
        (mu.toOuterMeasure
          (lemma79CanonicalEndpointFreshEStarAt
            entry family base Kcut p)).toReal := by
        simpa [mu, allowed] using
          (lemma79CanonicalEndpointFreshEStarEvent_toReal_le_sum
            mu entry family base Kcut T R)
    _ ≤ ∑ p ∈ allowed,
        (taoSection7Case3BaseKcutPolynomialBudgetTerm
            constants Aweight base Kcut p +
          taoSection7Case3BaseKcutExponentialBudgetTerm
            constants Aweight p) := by
      exact Finset.sum_le_sum hrow
    _ ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) := by
      exact
        TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.sum_canonicalTerms_le
          (by simpa [allowed] using habsorb)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
