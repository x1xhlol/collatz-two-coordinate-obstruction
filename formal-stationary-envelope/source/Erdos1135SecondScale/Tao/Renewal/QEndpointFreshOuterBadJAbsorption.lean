/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOuterBadJ
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Canonical OuterBadJ Scalar Absorption

This leaf absorbs the fixed-P exponential large-horizontal tail against any
fixed natural polynomial weight.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A fixed polynomial times the canonical one-rate envelope is eventually at
most one half. -/
theorem exists_natCast_pow_mul_outerBadJRate_le_half
    {K c : ℝ} (_hK : 0 < K) (hc : 0 < c) (B P : ℕ) :
    ∃ C : ℕ, ∀ m : ℕ, C ≤ m →
      (m : ℝ) ^ B * (K + Real.exp ((P : ℝ) / 2)) *
          Real.exp (-c * (m : ℝ)) ≤ 1 / 2 := by
  have hlim :
      Filter.Tendsto
        (fun m : ℕ =>
          (m : ℝ) ^ B * (K + Real.exp ((P : ℝ) / 2)) *
            Real.exp (-c * (m : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, mul_assoc,
      mul_comm, mul_left_comm, zero_mul] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          (B : ℝ) c hc).comp tendsto_natCast_atTop_atTop).mul_const
        (K + Real.exp ((P : ℝ) / 2))
  rcases Filter.eventually_atTop.1
      (hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)) with
    ⟨C, hC⟩
  exact ⟨C, hC⟩

/-- Fixed-parameter large-horizontal mass is eventually absorbed by the first
half of the outer priority budget. -/
theorem
    lemma79CanonicalEndpointFreshPMF_outerBadJ_weighted_toReal_le_half
    (B P : ℕ) :
    ∃ C : ℕ, ∀ {J : ℕ}, P ≤ J →
      ∀ (entry : TaoSection7RenewalPoint) (gap m : ℕ), C ≤ m →
        (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ) →
        (m : ℝ) ^ B *
          ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
            {atom |
              9 * m ≤ 10 *
                (atom.1.1 +
                  lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
          1 / 2 := by
  rcases
      lemma79CanonicalEndpointFreshPMF_outerBadJ_singleRate_toReal_le with
    ⟨K, c, hK, hc, htail⟩
  rcases exists_natCast_pow_mul_outerBadJRate_le_half
      (K := K) (c := c) hK hc B P with
    ⟨C, hC⟩
  refine ⟨max 1 C, ?_⟩
  intro J hPJ entry gap m hm hgap
  have hm1 : 1 ≤ m :=
    le_trans (Nat.le_max_left 1 C) hm
  have hCm : C ≤ m :=
    le_trans (Nat.le_max_right 1 C) hm
  have hmass :=
    htail hPJ entry gap m hm1 hgap
  calc
    (m : ℝ) ^ B *
        ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
          {atom |
            9 * m ≤ 10 *
              (atom.1.1 +
                lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
      (m : ℝ) ^ B *
        ((K + Real.exp ((P : ℝ) / 2)) *
          Real.exp (-c * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (m : ℝ) ^ B * (K + Real.exp ((P : ℝ) / 2)) *
          Real.exp (-c * (m : ℝ)) := by ring
    _ ≤ 1 / 2 := hC m hCm

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
