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
import Erdos1135Predecessor.Tao.Renewal.Outer736HoldExpectation

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

open scoped BigOperators

noncomputable section

theorem explicitRenewal_geom4_moment (A : ℕ) :
    taoSection7Geom4PolynomialMoment A ≤ (A.factorial : ℝ) * 4 ^ A := by
  have hmoment := (polynomialGeometric_moment_le A
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).2
  have heq : taoSection7Geom4PolynomialMoment A = (1 / 4 : ℝ) *
      ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ A * (3 / 4 : ℝ) ^ k := by
    unfold taoSection7Geom4PolynomialMoment
    rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [Equiv.pnatEquivNat_symm_apply]
    have hmass : (geom4PNat k.succPNat).toReal = (1 / 4 : ℝ) * (3 / 4 : ℝ) ^ k := by
      simpa using geom4PNat_apply_nat_succ_toReal k
    rw [hmass]
    have hk : ((k.succPNat : ℕ+) : ℕ) = k + 1 := rfl
    rw [hk]
    ring
  rw [heq]
  apply (mul_le_mul_of_nonneg_left hmoment (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans
  apply le_of_eq
  norm_num only [show (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num]
  rw [div_pow, one_pow, pow_succ]
  field_simp

theorem explicitRenewal_geom4_moment_pow (A : ℕ) :
    taoSection7Geom4PolynomialMoment A ≤ (4 * (A : ℝ)) ^ A := by
  have hfact : (A.factorial : ℝ) ≤ (A : ℝ) ^ A := by
    exact_mod_cast Nat.factorial_le_pow A
  calc
    _ ≤ (A.factorial : ℝ) * 4 ^ A := explicitRenewal_geom4_moment A
    _ ≤ (A : ℝ) ^ A * 4 ^ A := mul_le_mul_of_nonneg_right hfact (by positivity)
    _ = _ := by rw [mul_pow]; ring

end

end Erdos1135Predecessor.ND.PositiveDensity
