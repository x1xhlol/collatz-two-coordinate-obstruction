/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Lemma74ClaimStarScalars

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

noncomputable def lemma79R2ContractionFactor : ℝ :=
  1 - (1 - Real.exp (-1)) / 2

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

end Erdos1135Predecessor
