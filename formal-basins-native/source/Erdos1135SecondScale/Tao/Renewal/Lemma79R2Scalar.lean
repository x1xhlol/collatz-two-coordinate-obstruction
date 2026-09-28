/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Lemma74ClaimStarScalars

/-!
# Lemma 7.9 Killed R=2 Scalar Contraction

This proof leaf verifies the scalar contraction supplied by canonical
localized exit-white mass one half.  Claim-Star smallness already gives enough
room; no additional epsilon selector is required for the repaired `R=2`
pilot.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Contraction factor obtained when at least half the endpoint mass pays one
additional white-hit factor `exp(-1)`. -/
noncomputable def lemma79R2ContractionFactor : ℝ :=
  1 - (1 - Real.exp (-1)) / 2

/-- The half-mass contraction is bounded by `exp(-epsilon)` throughout the
Claim-Star scalar regime. -/
theorem lemma79R2ContractionFactor_le_exp_neg
    {epsilon : ℝ}
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    lemma79R2ContractionFactor ≤ Real.exp (-epsilon) := by
  have hexpOne : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hexpNegOne : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hexpOne)
  have hfactor :
      lemma79R2ContractionFactor ≤ (3 / 4 : ℝ) := by
    unfold lemma79R2ContractionFactor
    linarith
  have hepsilon := hscalar.epsilon_le_one_hundredth
  have hthreeQuarter : (3 / 4 : ℝ) ≤ 1 - epsilon := by
    linarith
  exact hfactor.trans (hthreeQuarter.trans (Real.one_sub_le_exp_neg epsilon))

/-- Absorb one `R=2` contraction factor into one of the two epsilon rewards. -/
theorem lemma79_exp_add_two_epsilon_mul_r2Contraction_le
    {epsilon x : ℝ}
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon) :
    Real.exp (x + 2 * epsilon) * lemma79R2ContractionFactor ≤
      Real.exp (x + epsilon) := by
  calc
    Real.exp (x + 2 * epsilon) * lemma79R2ContractionFactor ≤
        Real.exp (x + 2 * epsilon) * Real.exp (-epsilon) :=
      mul_le_mul_of_nonneg_left
        (lemma79R2ContractionFactor_le_exp_neg hscalar)
        (Real.exp_pos _).le
    _ = Real.exp (x + epsilon) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
