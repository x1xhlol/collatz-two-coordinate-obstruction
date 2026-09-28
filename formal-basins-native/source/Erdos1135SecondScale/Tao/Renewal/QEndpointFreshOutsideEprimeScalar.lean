/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeMass

/-!
# Canonical Outside-Eprime Scalar Scales

This proof leaf records the sharp large-branch scale choice used after the
canonical outside-`E'_p` mass theorem.  For
`X = Aweight^2 * (p + 1)`, it chooses geometric scales `2`, `X`, `2X`, and
radius `3X`, and proves the deterministic absorption and separation facts
from the branch hypothesis `30X <= sMin`.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Lemma710

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Natural sharp scale `Aweight^2 * (p + 1)`. -/
def lemma79OutsideEprimeScaleNat (Aweight p : ℕ) : ℕ :=
  Aweight ^ 2 * (p + 1)

/-- Real coercion of the sharp natural scale. -/
def lemma79OutsideEprimeScale (Aweight p : ℕ) : ℝ :=
  lemma79OutsideEprimeScaleNat Aweight p

/-- Natural localization radius `3 * Aweight^2 * (p + 1)`. -/
def lemma79OutsideEprimeRadius (Aweight p : ℕ) : ℕ :=
  3 * lemma79OutsideEprimeScaleNat Aweight p

/-- Exact rational upper bound for Tao's horizontal logarithmic slope. -/
theorem taoSection7_log2_div_log9_lt_two_fifths :
    Real.log 2 / Real.log 9 < (2 / 5 : ℝ) := by
  have hlog9 : 0 < Real.log (9 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ 5 < (9 : ℝ) ^ 2 := by norm_num
  have hp := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hp
  apply (div_lt_iff₀ hlog9).2
  calc
    Real.log 2 = (5 * Real.log 2) / 5 := by ring
    _ < (2 * Real.log 9) / 5 :=
      div_lt_div_of_pos_right hp (by norm_num)
    _ = (2 / 5 : ℝ) * Real.log 9 := by ring

/-- The geometric separation coefficient is at most one tenth. -/
theorem sigmaSeparationScale_le_one_tenth
    {sMin : ℝ} (hsMin : 0 ≤ sMin) :
    sigmaSeparationScale sMin ≤ sMin / 10 := by
  have hlog9 : Real.log (9 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hratio : Real.log 2 / Real.log 9 ≤ (2 / 5 : ℝ) :=
    taoSection7_log2_div_log9_lt_two_fifths.le
  have hcoeff :
      Real.log 2 / (4 * Real.log 9) =
        (Real.log 2 / Real.log 9) / 4 := by
    field_simp [hlog9]
  unfold sigmaSeparationScale
  rw [hcoeff]
  nlinarith [mul_le_mul_of_nonneg_right hratio hsMin]

/-- The geometric separation coefficient is strictly larger than one
sixteenth on positive scales. -/
theorem one_sixteenth_mul_lt_sigmaSeparationScale
    {sMin : ℝ} (hsMin : 0 < sMin) :
    sMin / 16 < sigmaSeparationScale sMin := by
  have hlog9 : Real.log (9 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hratio := lemma710_log_margin_pos
  have hcoeff :
      Real.log 2 / (4 * Real.log 9) =
        (Real.log 2 / Real.log 9) / 4 := by
    field_simp [hlog9]
  unfold sigmaSeparationScale
  rw [hcoeff]
  have hmul := mul_lt_mul_of_pos_right hratio (show 0 < sMin / 4 by positivity)
  nlinarith

/-- Flooring the separation scale loses at most a factor two once
`sMin >= 32`. -/
theorem sMin_div_thirty_two_lt_floor_sigmaSeparationScale
    {sMin : ℝ} (hsMin : 32 ≤ sMin) :
    sMin / 32 < (Nat.floor (sigmaSeparationScale sMin) : ℝ) := by
  have hlower := one_sixteenth_mul_lt_sigmaSeparationScale
    (show 0 < sMin by linarith)
  have hfloor :
      sigmaSeparationScale sMin <
        (Nat.floor (sigmaSeparationScale sMin) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  nlinarith

/-- Deterministic facts supplied by the large branch `30X <= sMin`. -/
structure Lemma79OutsideEprimeLargeBranchScaleData
    (Aweight p : ℕ) (sMin : ℝ) : Prop where
  gap_absorbs :
    TaoSection7Triangle.lemma710GapAbsorbs
      2 (lemma79OutsideEprimeScale Aweight p) sMin
  sourceJ :
    (Real.log 2 / Real.log 9) *
        (2 * lemma79OutsideEprimeScale Aweight p +
          2 * lemma79OutsideEprimeScale Aweight p) ≤
      2 * lemma79OutsideEprimeScale Aweight p
  radius_absorbs :
    (2 * lemma79OutsideEprimeScale Aweight p) ^ 2 +
        (2 * lemma79OutsideEprimeScale Aweight p) ^ 2 ≤
      (lemma79OutsideEprimeRadius Aweight p : ℝ) ^ 2
  radius_le_tenth :
    (lemma79OutsideEprimeRadius Aweight p : ℝ) ≤ sMin / 10
  separation_ge_one : 1 ≤ sigmaSeparationScale sMin
  window_card_le :
    (((2 * lemma79OutsideEprimeRadius Aweight p + 1 : ℕ) : ℝ)) ≤
      7 * lemma79OutsideEprimeScale Aweight p
  floor_separation_lower :
    sMin / 32 < (Nat.floor (sigmaSeparationScale sMin) : ℝ)

/-- The source schedule lower bound `Aweight >= 3` and the large branch
`30X <= sMin` produce all sharp geometry and floor-separation facts. -/
theorem lemma79OutsideEprimeLargeBranchScaleData_of_thirty_mul_le
    {Aweight p : ℕ} {sMin : ℝ}
    (hAweight : 3 ≤ Aweight)
    (h30 : 30 * lemma79OutsideEprimeScale Aweight p ≤ sMin) :
    Lemma79OutsideEprimeLargeBranchScaleData Aweight p sMin := by
  let Xnat := lemma79OutsideEprimeScaleNat Aweight p
  let X : ℝ := lemma79OutsideEprimeScale Aweight p
  let R := lemma79OutsideEprimeRadius Aweight p
  have hA2 : 9 ≤ Aweight ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hAweight hAweight
  have hXnat9 : 9 ≤ Xnat := by
    apply hA2.trans
    dsimp [Xnat, lemma79OutsideEprimeScaleNat]
    simpa using Nat.mul_le_mul_left (Aweight ^ 2)
      (show 1 ≤ p + 1 by omega)
  have hXone : (1 : ℝ) ≤ X := by
    have hXnat1 : 1 ≤ Xnat := le_trans (by norm_num) hXnat9
    have hcast : (1 : ℝ) ≤ (Xnat : ℝ) := by exact_mod_cast hXnat1
    simpa [X, Xnat, lemma79OutsideEprimeScale] using hcast
  have hX0 : 0 ≤ X := le_trans (by norm_num) hXone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hgap : TaoSection7Triangle.lemma710GapAbsorbs 2 X sMin := by
    unfold TaoSection7Triangle.lemma710GapAbsorbs
    refine ⟨hX0, by norm_num, ?_⟩
    have hquarter : 2 * X + 1 ≤ sMin / 4 := by
      nlinarith [h30, hXone]
    calc
      (Real.log 2 / Real.log 9) * (2 * X + 1) ≤
          (Real.log 2 / Real.log 9) * (sMin / 4) :=
        mul_le_mul_of_nonneg_left hquarter (div_pos hlog2 hlog9).le
      _ = (Real.log 2 / (4 * Real.log 9)) * sMin := by
        field_simp [ne_of_gt hlog9]
  have hsourceJ :
      (Real.log 2 / Real.log 9) * (2 * X + 2 * X) ≤ 2 * X := by
    have hhalf : Real.log 2 / Real.log 9 ≤ (1 / 2 : ℝ) := by
      linarith [lemma710_log_margin_le_quarter]
    calc
      (Real.log 2 / Real.log 9) * (2 * X + 2 * X) =
          (Real.log 2 / Real.log 9) * (4 * X) := by ring
      _ ≤ (1 / 2 : ℝ) * (4 * X) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = 2 * X := by ring
  have hRcast : (R : ℝ) = 3 * X := by
    simp [R, X, lemma79OutsideEprimeRadius,
      lemma79OutsideEprimeScale, lemma79OutsideEprimeScaleNat]
  have hradius : (2 * X) ^ 2 + (2 * X) ^ 2 ≤ (R : ℝ) ^ 2 := by
    rw [hRcast]
    nlinarith [sq_nonneg X]
  have hRle : (R : ℝ) ≤ sMin / 10 := by
    rw [hRcast]
    nlinarith [h30]
  have hsMin32 : (32 : ℝ) ≤ sMin := by
    have hXnine : (9 : ℝ) ≤ X := by
      have hcast : (9 : ℝ) ≤ (Xnat : ℝ) := by exact_mod_cast hXnat9
      simpa [X, Xnat, lemma79OutsideEprimeScale] using hcast
    nlinarith [h30]
  have hsepOne : 1 ≤ sigmaSeparationScale sMin := by
    have hlower := one_sixteenth_mul_lt_sigmaSeparationScale
      (show 0 < sMin by linarith)
    nlinarith
  have hwindowNat : 2 * R + 1 ≤ 7 * Xnat := by
    dsimp [R, lemma79OutsideEprimeRadius]
    omega
  have hwindow : ((2 * R + 1 : ℕ) : ℝ) ≤ 7 * X := by
    have hcast : ((2 * R + 1 : ℕ) : ℝ) ≤ ((7 * Xnat : ℕ) : ℝ) := by
      exact_mod_cast hwindowNat
    simpa [X, Xnat, lemma79OutsideEprimeScale] using hcast
  exact
    { gap_absorbs := by simpa [X] using hgap
      sourceJ := by simpa [X] using hsourceJ
      radius_absorbs := by simpa [X, R] using hradius
      radius_le_tenth := by simpa [R] using hRle
      separation_ge_one := hsepOne
      window_card_le := by simpa [X, R] using hwindow
      floor_separation_lower :=
        sMin_div_thirty_two_lt_floor_sigmaSeparationScale hsMin32 }

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
