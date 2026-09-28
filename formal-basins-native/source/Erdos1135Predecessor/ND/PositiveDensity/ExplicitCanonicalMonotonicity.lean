/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase2Threshold
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase3Threshold
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCollar
import Erdos1135Predecessor.Tao.Renewal.Prop78ActiveCover

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

def explicitRenewalMonotonicityThreshold
    {constants : TaoSection7Lemma710Constants} {A E : ℕ}
    (fixed : TaoSection7Case3FixedParameters constants A (explicitRenewalEpsilon E))
    (S0 L : ℕ) : ℕ :=
  max (explicitRenewalCase1Threshold A E)
    (max (explicitRenewalCase2Threshold A L E) (explicitRenewalCase3Threshold fixed S0))

theorem explicitRenewal_monotonicity
    {constants : TaoSection7Lemma710Constants} {A E : ℕ} (hA : 1 ≤ A)
    (fixed : TaoSection7Case3FixedParameters constants A (explicitRenewalEpsilon E))
    (S0 : ℕ) (hEStar : TaoSection7Case3CanonicalEStarData fixed S0)
    (L : ℕ)
    (hmass : ∀ start s,
      (1 / 2 : ℝ) ≤ ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    (hcollar : taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) ^ 2)
    (n : ℕ) (xi : ZMod (3 ^ n)) (hxi : zmodThreePrimitive n xi)
    (m : ℕ) (hm : explicitRenewalMonotonicityThreshold fixed S0 L ≤ m)
    (hm_hi : m ≤ n / 2) :
    taoSection7SourceActualQmAtCutoff n A m xi (explicitRenewalEpsilon E) ≤
      taoSection7SourceActualQmAtCutoff n A (m - 1) xi (explicitRenewalEpsilon E) := by
  let C := explicitRenewalMonotonicityThreshold fixed S0 L
  have hC1 : explicitRenewalCase1Threshold A E ≤ C := le_max_left _ _
  have hC2 : explicitRenewalCase2Threshold A L E ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : explicitRenewalCase3Threshold fixed S0 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hthreshold : TaoSection7Prop78Threshold A (explicitRenewalEpsilon E) C :=
    ⟨(le_max_left _ _).trans hC3⟩
  let hactive := TaoSection7Prop78ActiveCoverData.of_canonical hxi fixed.scalar
  have hcases : TaoSection7Prop78BoundaryCaseBounds
      n A m xi (explicitRenewalEpsilon E) hactive.family :=
    { cutoffWhite := by
        intro p hp hwhite
        have h := explicitRenewal_case1_halfDiscount (hC1.trans hm) hp hwhite
        have he : Real.exp (-(explicitRenewalEpsilon E ^ 3 / 2)) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have h0 : 0 ≤ explicitRenewalEpsilon E := fixed.scalar.epsilon_pos.le
          exact neg_nonpos.mpr (div_nonneg (pow_nonneg h0 _) (by norm_num))
        have hQ := taoSection7SourceActualQmAtCutoff_nonneg
          (n := n) (A := A) (m := m - 1) (xi := xi) fixed.scalar.epsilon_pos.le
        exact h.trans (by
          have hh := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ ((m : ℝ) ^ A)⁻¹)) hQ
          simpa only [one_mul] using hh)
      nearTop := by
        intro p hp hnear
        exact explicitRenewal_case2_nearTop A L E hA hmass hcollar
          n xi hactive m (hC2.trans hm) p hp hnear
      farBelow := by
        intro p hp hfar
        exact explicitRenewal_case3_farBelow fixed S0 hEStar L hmass hcollar
          n xi hxi m (hC3.trans hm) hm_hi p hp hfar }
  exact taoSection7_prop78_monotonicity_740_of_activeCover_caseBounds
    (C := C) fixed.scalar.epsilon_pos.le hthreshold hm hm_hi hactive hcases

end

end Erdos1135Predecessor.ND.PositiveDensity
