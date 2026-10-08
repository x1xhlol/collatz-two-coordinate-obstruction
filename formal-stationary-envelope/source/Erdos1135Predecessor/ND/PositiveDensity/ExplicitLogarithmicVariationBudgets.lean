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

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitRetainedGeometricTail
import Erdos1135Predecessor.ND.PositiveDensity.ExplicitVariationBudgets

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

@[irreducible] def explicitLogarithmicSeedGeneration (b C : ℕ) : ℕ :=
  20000 * (Nat.clog 2 (explicitCoreEnvelope b C) + 64)

@[irreducible] def explicitLogarithmicTerminalStart (b C e : ℕ) : ℕ :=
  20000 * (Nat.clog 2 ((e + 21) * explicitCoreEnvelope b C) + 96)

private theorem majorant_le_envelope {b : ℕ} (hb : 1 ≤ b) (C K n : ℕ)
    {c : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C) :
    ndRootCoreVariationMajorant b 17 K c n ≤
      (explicitCoreEnvelope b C : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ 3 * (9999 / 10000 : ℝ) ^ n) := by
  have hA := explicitCoreVariationCoefficient_le_envelope hb C K hc hcC
  calc
    _ ≤ ndExplicitCoreVariationCoefficient b 17 K c * ((n + 1 : ℕ) : ℝ) ^ 3 *
        (9999 / 10000 : ℝ) ^ n := rootCoreVariationMajorant_le_explicit b 17 K n hb hc
    _ = ndExplicitCoreVariationCoefficient b 17 K c *
        (((n + 1 : ℕ) : ℝ) ^ 3 * (9999 / 10000 : ℝ) ^ n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (by positivity)

theorem explicitCoreVariationTail_logarithmic_budget
    {b : ℕ} (hb : 1 ≤ b) (C K : ℕ) {c : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C)
    {N : ℕ} (hN : explicitLogarithmicSeedGeneration b C ≤ N) :
    ndRootCoreVariationTail b 17 K c N ≤ (1 / 16 : ℝ) := by
  have hs : Summable (fun j : ℕ => ndRootCoreVariationMajorant b 17 K c (N + j)) := by
    simpa only [Nat.add_comm N] using
      (summable_nat_add_iff N).mpr (summable_rootCoreVariationMajorant b 17 K c)
  have hp := (polynomialGeometric_moment_le 3 (r := (9999 / 10000 : ℝ))
    (by norm_num) (by norm_num)).1
  have ht : Summable (fun j : ℕ => ((N + j + 1 : ℕ) : ℝ) ^ 3 *
      (9999 / 10000 : ℝ) ^ (N + j)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).mpr hp
  have htail : (∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ 3 *
      (9999 / 10000 : ℝ) ^ (N + j)) ≤
      6 * 20000 ^ 4 * (19999 / 20000 : ℝ) ^ N := by
    convert polynomialGeometric_tail_le_slow_ratio 3 N using 1
  have hF := coefficient_mul_slowRatio_le (explicitCoreEnvelope b C) 64 N (by
    simpa only [explicitLogarithmicSeedGeneration] using hN)
  unfold ndRootCoreVariationTail
  calc
    _ ≤ ∑' j : ℕ, (explicitCoreEnvelope b C : ℝ) *
        (((N + j + 1 : ℕ) : ℝ) ^ 3 * (9999 / 10000 : ℝ) ^ (N + j)) :=
      hs.tsum_le_tsum (fun j => majorant_le_envelope hb C K (N + j) hc hcC) (ht.mul_left _)
    _ = (explicitCoreEnvelope b C : ℝ) *
        (∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ 3 * (9999 / 10000 : ℝ) ^ (N + j)) :=
      tsum_mul_left
    _ ≤ (explicitCoreEnvelope b C : ℝ) * (6 * 20000 ^ 4 * (19999 / 20000 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = (6 * 20000 ^ 4) * ((explicitCoreEnvelope b C : ℝ) * (19999 / 20000 : ℝ) ^ N) := by ring
    _ ≤ (6 * 20000 ^ 4) * (1 / (2 : ℝ) ^ 64) := mul_le_mul_of_nonneg_left hF (by positivity)
    _ ≤ _ := by norm_num

theorem explicitTerminalVariation_logarithmic_budget
    {b : ℕ} (hb : 1 ≤ b) (C e K : ℕ) {c : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C)
    {n : ℕ} (hn : explicitLogarithmicTerminalStart b C e ≤ n) :
    ndRootTerminalVariationMajorant b e 17 K c n ≤ (1 / 8 : ℝ) := by
  let H := (e + 21) * explicitCoreEnvelope b C
  have hp : ((n + 1 : ℕ) : ℝ) ^ 5 * (9999 / 10000 : ℝ) ^ n ≤
      120 * 20000 ^ 6 * (19999 / 20000 : ℝ) ^ n := by
    convert polynomialGeometric_term_le_slow_ratio 5 n using 1
  have hH := coefficient_mul_slowRatio_le H 96 n (by
    simpa only [explicitLogarithmicTerminalStart, H] using hn)
  unfold ndRootTerminalVariationMajorant
  calc
    _ ≤ ((e + 17 + 4 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 *
        ((explicitCoreEnvelope b C : ℝ) *
          (((n + 1 : ℕ) : ℝ) ^ 3 * (9999 / 10000 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left (majorant_le_envelope hb C K n hc hcC) (by positivity)
    _ = (H : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 5 * (9999 / 10000 : ℝ) ^ n) := by
      dsimp [H]
      push_cast
      ring
    _ ≤ (H : ℝ) * (120 * 20000 ^ 6 * (19999 / 20000 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = (120 * 20000 ^ 6) * ((H : ℝ) * (19999 / 20000 : ℝ) ^ n) := by ring
    _ ≤ (120 * 20000 ^ 6) * (1 / (2 : ℝ) ^ 96) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ _ := by norm_num

end

end Erdos1135Predecessor.ND.PositiveDensity
