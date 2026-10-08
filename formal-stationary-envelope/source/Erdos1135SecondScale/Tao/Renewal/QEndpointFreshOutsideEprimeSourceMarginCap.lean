/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.QEndpointFreshOutsideEprimeSourceMargin

/-!
# Canonical Outside-Eprime Fixed-Cap Source Margin

This leaf lifts the fixed-offset row-margin threshold to one threshold for
every offset below a fixed cap.  The cap is chosen before the source sample
and does not depend on the boundary scale.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The sharp scale `Aweight^2 * (p + 1)` is monotone in the offset. -/
theorem lemma79OutsideEprimeScale_mono_p
    (Aweight : ℕ) :
    Monotone (lemma79OutsideEprimeScale Aweight) := by
  intro p q hpq
  have hnat :
      lemma79OutsideEprimeScaleNat Aweight p ≤
        lemma79OutsideEprimeScaleNat Aweight q := by
    dsimp [lemma79OutsideEprimeScaleNat]
    exact Nat.mul_le_mul_left (Aweight ^ 2)
      (Nat.add_le_add_right hpq 1)
  change
    (lemma79OutsideEprimeScaleNat Aweight p : ℝ) ≤
      (lemma79OutsideEprimeScaleNat Aweight q : ℝ)
  exact_mod_cast hnat

/-- A single source-gap threshold controls the row margin for all offsets in
the fixed inclusive range `p <= Pmax`. -/
theorem exists_lemma79OutsideEprimeErrorMargin_cap_threshold
    (Aweight Pmax : ℕ) :
    ∃ S0 : ℕ, ∀ fpGap : ℕ, S0 ≤ fpGap →
      ∀ p : ℕ, p ≤ Pmax →
        2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
            ((Real.log 2 / Real.log 9) *
              (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
          (fpGap : ℝ) *
            (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  rcases
      exists_lemma79OutsideEprimeErrorMargin_threshold Aweight Pmax with
    ⟨S0, hS0⟩
  refine ⟨S0, ?_⟩
  intro fpGap hgap p hp
  have hcap := hS0 fpGap hgap
  have hscale :
      lemma79OutsideEprimeScale Aweight p ≤
        lemma79OutsideEprimeScale Aweight Pmax :=
    lemma79OutsideEprimeScale_mono_p Aweight hp
  have hratio0 : 0 ≤ Real.log 2 / Real.log 9 :=
    div_nonneg (Real.log_pos (by norm_num)).le
      (Real.log_pos (by norm_num)).le
  have hfixed :
      (Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1 ≤
        (Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight Pmax) + 1 := by
    gcongr
  calc
    2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight p) + 1) ≤
      2 * (fpGap : ℝ) ^ (3 / 5 : ℝ) +
        ((Real.log 2 / Real.log 9) *
          (2 * lemma79OutsideEprimeScale Aweight Pmax) + 1) :=
      by gcongr
    _ ≤ (fpGap : ℝ) *
        (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := hcap

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
