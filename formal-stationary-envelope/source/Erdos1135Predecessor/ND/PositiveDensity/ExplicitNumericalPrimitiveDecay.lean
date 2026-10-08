/-
Compatibility modification, 8 October 2026: proof elaboration and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalPrimitiveCoefficient

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

noncomputable section

attribute [local irreducible] explicitRenewal_fixed

private theorem threshold_data
    {constants : TaoSection7Lemma710Constants} {A E : ℕ}
    (fixed : TaoSection7Case3FixedParameters constants A (explicitRenewalEpsilon E))
    (S0 L : ℕ) : TaoSection7Prop78Threshold A (explicitRenewalEpsilon E)
      (explicitRenewalMonotonicityThreshold fixed S0 L) := by
  refine ⟨?_⟩
  exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

@[irreducible] def explicitRenewalPrimitiveCoefficientAt {E : ℕ}
    (hE : 20 ≤ E) (L : ℕ) : ℕ :=
  let fixed := explicitRenewal_fixed hE
  let C := explicitRenewalMonotonicityThreshold fixed (2 ^ 34 * (fixed.Pmax + 1)) L
  (32 * 6409 * C) ^ 6409

private theorem coefficient_cast (A C : ℕ) :
    (((32 * A * C) ^ A : ℕ) : ℝ) = (32 * (A : ℝ) * C) ^ A := by
  push_cast
  rfl

theorem explicitRenewal_fixedPrimitiveDecay {E : ℕ} (hE : 20 ≤ E)
    (L : ℕ)
    (hmass : ∀ start s,
      (1 / 2 : ℝ) ≤
        ((Tao.TaoSection7Lemma77.lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
          (Tao.TaoSection7Lemma77.lemma77CanonicalLocalizedEndpointEvent s L)).toReal)
    (hcollar : taoSection7Case2HorizontalCollar L ^ 2 + (L : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) ^ 2) :
    syracPMFPrimitivePolynomialDecayAt 6409 (explicitRenewalPrimitiveCoefficientAt hE L : ℝ) := by
  let scalar := explicitRenewal_scalar hE
  let fixed := explicitRenewal_fixed hE
  let S0 := 2 ^ 34 * (fixed.Pmax + 1)
  have hC := threshold_data fixed S0 L
  have hmono := explicitRenewal_monotonicity (by norm_num : 1 ≤ (6409 : ℕ))
    fixed S0 (explicitRenewal_canonicalEStar hE) L hmass hcollar
  have h := explicitRenewal_primitive_of_monotonicity scalar.epsilon_pos.le
    (scalar.epsilon_le_one_hundredth.trans (by norm_num)) hC hmono
  delta explicitRenewalPrimitiveCoefficientAt
  set_option exponentiation.threshold 8192 in
  exact (congrArg (syracPMFPrimitivePolynomialDecayAt 6409)
    (coefficient_cast 6409 (explicitRenewalMonotonicityThreshold fixed S0 L))).mpr h

private theorem numericalExponentGuard : 20 ≤ (2 : ℕ) ^ 170 := by norm_num

@[irreducible] def explicitRenewalPrimitiveCoefficient : ℕ :=
  explicitRenewalPrimitiveCoefficientAt numericalExponentGuard (2 ^ 80)

theorem explicitRenewal_numericalPrimitiveDecay :
    syracPMFPrimitivePolynomialDecayAt 6409 (explicitRenewalPrimitiveCoefficient : ℝ) := by
  delta explicitRenewalPrimitiveCoefficient
  exact explicitRenewal_fixedPrimitiveDecay numericalExponentGuard (2 ^ 80)
    explicitRenewal_numericalLocalizedMass explicitRenewal_numericalCollar

end

end Erdos1135Predecessor.ND.PositiveDensity
