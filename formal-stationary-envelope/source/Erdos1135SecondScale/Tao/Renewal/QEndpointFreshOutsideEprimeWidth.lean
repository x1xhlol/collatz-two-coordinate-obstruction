/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeScalar

/-!
# Canonical Outside-Eprime Kernel Widths

This proof leaf converts Tao's source-scale bounds into the two quadratic
kernel-width hypotheses used by the canonical outside-`E'_p` mass theorem.
The constant is deliberately explicit and non-asymptotic.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A uniform logarithmic estimate sufficient for the source-width
comparison. -/
theorem lemma79_log_sq_le_hundred_mul_rpow_one_fifth
    {M : ℝ} (hM : 1 ≤ M) :
    (Real.log M) ^ 2 ≤ 100 * M ^ (1 / 5 : ℝ) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlog_le :
      Real.log M ≤ 10 * M ^ (1 / 10 : ℝ) := by
    calc
      Real.log M ≤ M ^ (1 / 10 : ℝ) / (1 / 10 : ℝ) :=
        Real.log_le_rpow_div
          (x := M) (ε := (1 / 10 : ℝ)) hM0 (by norm_num)
      _ = 10 * M ^ (1 / 10 : ℝ) := by ring
  have hrpow_sq :
      (M ^ (1 / 10 : ℝ)) ^ (2 : ℕ) =
        M ^ (1 / 5 : ℝ) := by
    calc
      (M ^ (1 / 10 : ℝ)) ^ (2 : ℕ) =
          (M ^ (1 / 10 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (M ^ (1 / 10 : ℝ)) 2).symm
      _ = M ^ ((1 / 10 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hM0 (1 / 10 : ℝ) (2 : ℝ)).symm
      _ = M ^ (1 / 5 : ℝ) := by norm_num
  have hsq :
      (Real.log M) ^ 2 ≤
        (10 * M ^ (1 / 10 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog_le 2
  calc
    (Real.log M) ^ 2 ≤
        (10 * M ^ (1 / 10 : ℝ)) ^ 2 := hsq
    _ = 100 * (M ^ (1 / 10 : ℝ)) ^ 2 := by ring
    _ = 100 * M ^ (1 / 5 : ℝ) := by rw [hrpow_sq]

/-- Source admissibility and the far-below first-passage gap force the master
quadratic width comparison. -/
theorem lemma79_sMin_sq_le_hundred_mul_gap
    {M sMin gap : ℝ}
    (hM : 1 < M)
    (hsMin_nonneg : 0 ≤ sMin)
    (hsMin_le : sMin ≤ M ^ (2 / 5 : ℝ))
    (hgap : M / (Real.log M) ^ 2 ≤ gap) :
    sMin ^ 2 ≤ 100 * gap := by
  have hMpos : 0 < M := lt_trans (by norm_num) hM
  have hM0 : 0 ≤ M := hMpos.le
  have hlogpos : 0 < Real.log M := Real.log_pos hM
  have hlog_sq_pos : 0 < (Real.log M) ^ 2 := pow_pos hlogpos 2
  have hlog_bound :=
    lemma79_log_sq_le_hundred_mul_rpow_one_fifth hM.le
  have htwo_fifths_sq :
      (M ^ (2 / 5 : ℝ)) ^ (2 : ℕ) =
        M ^ (4 / 5 : ℝ) := by
    calc
      (M ^ (2 / 5 : ℝ)) ^ (2 : ℕ) =
          (M ^ (2 / 5 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (M ^ (2 / 5 : ℝ)) 2).symm
      _ = M ^ ((2 / 5 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hM0 (2 / 5 : ℝ) (2 : ℝ)).symm
      _ = M ^ (4 / 5 : ℝ) := by norm_num
  have hsMin_sq : sMin ^ 2 ≤ M ^ (4 / 5 : ℝ) := by
    have hsq :=
      pow_le_pow_left₀ hsMin_nonneg hsMin_le 2
    simpa [htwo_fifths_sq] using hsq
  have hpow_sum :
      M ^ (4 / 5 : ℝ) * M ^ (1 / 5 : ℝ) = M := by
    calc
      M ^ (4 / 5 : ℝ) * M ^ (1 / 5 : ℝ) =
          M ^ ((4 / 5 : ℝ) + (1 / 5 : ℝ)) :=
        (Real.rpow_add hMpos (4 / 5 : ℝ) (1 / 5 : ℝ)).symm
      _ = M ^ (1 : ℝ) := by norm_num
      _ = M := by simp
  have hcross :
      sMin ^ 2 * (Real.log M) ^ 2 ≤ 100 * M := by
    calc
      sMin ^ 2 * (Real.log M) ^ 2 ≤
          M ^ (4 / 5 : ℝ) * (Real.log M) ^ 2 :=
        mul_le_mul_of_nonneg_right hsMin_sq (sq_nonneg _)
      _ ≤ M ^ (4 / 5 : ℝ) *
          (100 * M ^ (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_bound (Real.rpow_nonneg hM0 _)
      _ = 100 * (M ^ (4 / 5 : ℝ) * M ^ (1 / 5 : ℝ)) := by ring
      _ = 100 * M := by rw [hpow_sum]
  have hdiv :
      sMin ^ 2 ≤ 100 * (M / (Real.log M) ^ 2) := by
    rw [show 100 * (M / (Real.log M) ^ 2) =
        (100 * M) / (Real.log M) ^ 2 by ring]
    exact (le_div_iff₀ hlog_sq_pos).2 hcross
  exact hdiv.trans (mul_le_mul_of_nonneg_left hgap (by norm_num))

/-- The master source-width comparison supplies both quadratic hypotheses of
the canonical outside-`E'_p` kernel theorem. -/
theorem lemma79OutsideEprimeKernelWidths_of_sourceScale
    {M sMin : ℝ} {fpGap R : ℕ}
    (hM : 1 < M)
    (hsMin_nonneg : 0 ≤ sMin)
    (hsMin_le : sMin ≤ M ^ (2 / 5 : ℝ))
    (hgap : M / (Real.log M) ^ 2 ≤ (fpGap : ℝ))
    (hR : (R : ℝ) ≤ sMin / 10) :
    (R : ℝ) ^ 2 ≤ 1 + (fpGap : ℝ) ∧
      (sigmaSeparationScale sMin) ^ 2 ≤ 1 + (fpGap : ℝ) := by
  have hmaster :
      sMin ^ 2 ≤ 100 * (fpGap : ℝ) :=
    lemma79_sMin_sq_le_hundred_mul_gap
      hM hsMin_nonneg hsMin_le hgap
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hR_sq :
      (R : ℝ) ^ 2 ≤ (sMin / 10) ^ 2 :=
    pow_le_pow_left₀ hR0 hR 2
  have hR_gap : (R : ℝ) ^ 2 ≤ (fpGap : ℝ) := by
    nlinarith [hmaster]
  have hsep0 : 0 ≤ sigmaSeparationScale sMin := by
    unfold sigmaSeparationScale
    positivity
  have hsep_le :
      sigmaSeparationScale sMin ≤ sMin / 10 :=
    sigmaSeparationScale_le_one_tenth hsMin_nonneg
  have hsep_sq :
      (sigmaSeparationScale sMin) ^ 2 ≤
        (sMin / 10) ^ 2 :=
    pow_le_pow_left₀ hsep0 hsep_le 2
  have hsep_gap :
      (sigmaSeparationScale sMin) ^ 2 ≤ (fpGap : ℝ) := by
    nlinarith [hmaster]
  constructor <;> nlinarith

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
