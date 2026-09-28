/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitPolynomialGeometricTail
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalShiftImageRate

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem rootCore_mixing_ratio_le_explicit :
    ndRootCoreGrowth * (200 / 201 : ℝ) ^ 6 ≤ 9999 / 10000 := by
  norm_num [ndRootCoreGrowth]

theorem rootCore_cap_ratio_le_explicit :
    ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ) ≤ 9999 / 10000 := by
  have he : ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ 100 = (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hp : (ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ 100 ≤
      (9999 / 10000 : ℝ) ^ 100 := by
    rw [mul_pow, he]
    norm_num [ndRootCoreGrowth]
  by_contra hn
  have hh := pow_lt_pow_left₀ (lt_of_not_ge hn) (by norm_num : (0 : ℝ) ≤ 9999 / 10000)
    (by decide : 100 ≠ 0)
  linarith

def ndExplicitCoreVariationCoefficient (b L K0 : ℕ) (C : ℝ) : ℝ :=
  ((4 * (b : ℝ) + 1) * (L + 5) * ((2 : ℝ) ^ (b + 1) + (16 : ℝ) ^ b)) *
    (2 / 3 : ℝ) * (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6) +
      (1 / 2 : ℝ) ^ K0)

theorem rootCoreVariationMajorant_le_explicit (b L K0 n : ℕ) (hb : 1 ≤ b)
    {C : ℝ} (hC : 0 ≤ C) :
    ndRootCoreVariationMajorant b L K0 C n ≤
      ndExplicitCoreVariationCoefficient b L K0 C * ((n + 1 : ℕ) : ℝ) ^ 3 *
        (9999 / 10000 : ℝ) ^ n := by
  have hbpow : (b : ℝ) ^ (3 / 5 : ℝ) ≤ b :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hb) (by norm_num)
  have hm := pow_le_pow_left₀ (by norm_num [ndRootCoreGrowth] :
    0 ≤ ndRootCoreGrowth * (200 / 201 : ℝ) ^ 6) rootCore_mixing_ratio_le_explicit n
  have hc := pow_le_pow_left₀ (by unfold ndRootCoreGrowth; positivity :
    0 ≤ ndRootCoreGrowth * (1 / 2 : ℝ) ^ (1 / 100 : ℝ)) rootCore_cap_ratio_le_explicit n
  have hmix : 0 ≤ (2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 := by
    unfold ndRootCoreStripConstant; positivity
  unfold ndRootCoreVariationMajorant ndExplicitCoreVariationCoefficient
  calc
    _ ≤ ((4 * (b : ℝ) + 1) * (L + 5) * ((2 : ℝ) ^ (b + 1) + (16 : ℝ) ^ b)) *
        (2 / 3 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 3 *
        (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6) *
          (9999 / 10000 : ℝ) ^ n + (1 / 2 : ℝ) ^ K0 * (9999 / 10000 : ℝ) ^ n) := by
      gcongr
      unfold ndRootCoreGrowth
      positivity
    _ = _ := by ring

end

end Erdos1135Predecessor.ND.PositiveDensity
