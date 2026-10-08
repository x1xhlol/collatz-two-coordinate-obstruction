/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
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

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase3Parameters
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2Geometry

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao Tao.TaoSection7Lemma77

noncomputable section

theorem explicitRenewal_collar_bound {B : ℕ} (hB : 1 ≤ B) :
    taoSection7Case2HorizontalCollar B ≤ 6 * (B : ℝ) ^ 2 := by
  let d := taoSection7Case2TopRowDrift
  have hd : (1 / 16 : ℝ) ≤ d ∧ d ≤ 3 / 20 := by
    have h := explicitRenewal_log_margin_bounds
    dsimp [d, taoSection7Case2TopRowDrift, taoSection7Case2TopRowSlope]
    constructor <;> linarith [h.1, h.2]
  have hd0 : 0 < 4 * d := by linarith [hd.1]
  have hquot : (B : ℝ) ^ 2 / (4 * d) ≤ 4 * (B : ℝ) ^ 2 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd.1 (sq_nonneg (B : ℝ))]
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  change 1 + d + (B : ℝ) ^ 2 / (4 * d) ≤ _
  nlinarith [hd.2]

theorem explicitRenewal_separation_eq (E : ℕ) :
    taoSection7TriangleSeparation (explicitRenewalEpsilon E) =
      (E : ℝ) * Real.log 2 / 10 := by
  unfold taoSection7TriangleSeparation taoSection7TriangleLogScale explicitRenewalEpsilon
  simp only [one_div, inv_inv, Real.log_pow]
  ring

theorem explicitRenewal_collar {B E : ℕ} (hB : 1 ≤ B)
    (hE : 160 * B ^ 2 ≤ E) :
    taoSection7Case2HorizontalCollar B ^ 2 + (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) ^ 2 := by
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hEreal : (160 : ℝ) * (B : ℝ) ^ 2 ≤ E := by exact_mod_cast hE
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hsep : 8 * (B : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon E) := by
    rw [explicitRenewal_separation_eq]
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg E)]
  have hC := explicitRenewal_collar_bound hB
  have hC0 := (taoSection7Case2HorizontalCollar_pos B).le
  have hCsq := mul_le_mul hC hC hC0 (by positivity : 0 ≤ 6 * (B : ℝ) ^ 2)
  have hSsq := mul_le_mul hsep hsep (by positivity : 0 ≤ 8 * (B : ℝ) ^ 2)
    (by nlinarith : 0 ≤ taoSection7TriangleSeparation (explicitRenewalEpsilon E))
  nlinarith [sq_nonneg ((B : ℝ) ^ 2 - 1)]

theorem explicitRenewal_numericalCollar :
    taoSection7Case2HorizontalCollar (2 ^ 80) ^ 2 + ((2 ^ 80 : ℕ) : ℝ) ^ 2 ≤
      taoSection7TriangleSeparation (explicitRenewalEpsilon (2 ^ 170)) ^ 2 :=
  explicitRenewal_collar (by norm_num) (by norm_num)

theorem explicitRenewal_numericalLocalizedMass (start : TaoSection7RenewalPoint) (s : ℕ) :
    (1 / 2 : ℝ) ≤
      ((lemma77CanonicalFirstPassageEndpointPMF start s).toOuterMeasure
        (lemma77CanonicalLocalizedEndpointEvent s (2 ^ 80))).toReal :=
  explicitRenewal_localized_mass (by rfl) start s

end

end Erdos1135Predecessor.ND.PositiveDensity
