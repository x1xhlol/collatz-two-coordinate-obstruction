/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitCoreProduct
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitVariationTail

namespace Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitCoreEnvelope (b C : ℕ) : ℕ :=
  2 ^ 467 * b * 16 ^ b * (C + 1)

private theorem envelope_cast (b C : ℕ) :
    (explicitCoreEnvelope b C : ℝ) = (2 : ℝ) ^ 467 * b * 16 ^ b * (C + 1) := by
  delta explicitCoreEnvelope
  push_cast
  rfl

set_option exponentiation.threshold 512 in
theorem explicitCoreVariationCoefficient_le_envelope
    {b : ℕ} (hb : 1 ≤ b) (C K : ℕ) {c : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C) :
    ndExplicitCoreVariationCoefficient b 17 K c ≤ (explicitCoreEnvelope b C : ℝ) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (1 : ℝ) ≤ (b : ℝ) ^ 6 := one_le_pow₀ hbR
  have htwo : (2 : ℝ) ^ (b + 1) ≤ (16 : ℝ) ^ b := by
    calc
      _ ≤ (2 : ℝ) ^ (4 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have hcap : (1 / 2 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hS := rootCoreStripConstant_le_explicit
  have hnum : 0 ≤ 2 * c * 8 ^ 6 + ndRootCoreStripConstant := by
    unfold ndRootCoreStripConstant
    positivity
  have hdiv : (2 * c * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 ≤
      2 * c * 8 ^ 6 + ndRootCoreStripConstant := div_le_self hnum hpow
  have hbracket : ((2 * c * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6) +
      (1 / 2 : ℝ) ^ K ≤ (2 : ℝ) ^ 459 * (C + 1) := by
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    nlinarith
  have hfac : ((4 * (b : ℝ) + 1) * (17 + 5) *
      ((2 : ℝ) ^ (b + 1) + 16 ^ b)) * (2 / 3 : ℝ) ≤
        220 * (b : ℝ) * 16 ^ b := by
    have ht : 0 ≤ (16 : ℝ) ^ b := by positivity
    calc
      _ ≤ (5 * (b : ℝ) * 22 * (2 * 16 ^ b)) * 1 := by
        gcongr <;> linarith
      _ = _ := by ring
  rw [envelope_cast]
  unfold ndExplicitCoreVariationCoefficient
  calc
    _ ≤ (220 * (b : ℝ) * 16 ^ b) * ((2 : ℝ) ^ 459 * (C + 1)) := by
      apply mul_le_mul hfac hbracket
      · positivity
      · positivity
    _ ≤ _ := by
      have hcoef : (220 : ℝ) * 2 ^ 459 ≤ 2 ^ 467 := by norm_num
      have h := mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ (b : ℝ) * 16 ^ b * (C + 1) by positivity)
      nlinarith only [h]

end

end Erdos1135Predecessor.ND.PositiveDensity
