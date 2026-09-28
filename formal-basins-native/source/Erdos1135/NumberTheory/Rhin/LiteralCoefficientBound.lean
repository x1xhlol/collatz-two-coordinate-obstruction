import Erdos1135.NumberTheory.Rhin.LiteralSupport
import Erdos1135.NumberTheory.Rhin.LiteralRemainder

/-!
# Coefficient growth for Rhin's literal square

This module proves the exact base-`24` coefficient bound consumed by the
three common-scale p. 159 row denominators.  The six bases are the coefficient
sums of the positive companions of the source factors; no coefficient table
is used.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

private theorem literalRhinRoundedCoefficientCertificate :
    4 ^ 705 * 3 ^ 553 * 5 ^ 448 * 17 ^ 110 * 263 ^ 39 * 271 ^ 55 ≤
      24 ^ 1000 := by
  set_option exponentiation.threshold 1000 in
    norm_num

private theorem literalRhinRawCoefficientProduct_le_explicit (n : ℕ) :
    4 ^ literalRhinMultiplicity 0 n *
      3 ^ literalRhinMultiplicity 1 n *
      5 ^ literalRhinMultiplicity 2 n *
      17 ^ literalRhinMultiplicity 3 n *
      263 ^ literalRhinMultiplicity 4 n *
      271 ^ literalRhinMultiplicity 5 n ≤
        24 ^ n := by
  have hm1 := literalRhinMultiplicity_upper n (0 : Fin 6)
  have hm2 := literalRhinMultiplicity_upper n (1 : Fin 6)
  have hm3 := literalRhinMultiplicity_upper n (2 : Fin 6)
  have hm4 := literalRhinMultiplicity_upper n (3 : Fin 6)
  have hm5 := literalRhinMultiplicity_upper n (4 : Fin 6)
  have hm6 := literalRhinMultiplicity_upper n (5 : Fin 6)
  simp only [literalRhinUpperExponent] at hm1 hm2 hm3 hm4 hm5 hm6
  have hp1 := Nat.pow_le_pow_right (by norm_num : 0 < 4) hm1
  have hp2 := Nat.pow_le_pow_right (by norm_num : 0 < 3) hm2
  have hp3 := Nat.pow_le_pow_right (by norm_num : 0 < 5) hm3
  have hp4 := Nat.pow_le_pow_right (by norm_num : 0 < 17) hm4
  have hp5 := Nat.pow_le_pow_right (by norm_num : 0 < 263) hm5
  have hp6 := Nat.pow_le_pow_right (by norm_num : 0 < 271) hm6
  apply (Nat.pow_le_pow_iff_left (by norm_num : (1000 : ℕ) ≠ 0)).mp
  calc
    (4 ^ literalRhinMultiplicity 0 n *
        3 ^ literalRhinMultiplicity 1 n *
        5 ^ literalRhinMultiplicity 2 n *
        17 ^ literalRhinMultiplicity 3 n *
        263 ^ literalRhinMultiplicity 4 n *
        271 ^ literalRhinMultiplicity 5 n) ^ 1000 =
      4 ^ (1000 * literalRhinMultiplicity 0 n) *
        3 ^ (1000 * literalRhinMultiplicity 1 n) *
        5 ^ (1000 * literalRhinMultiplicity 2 n) *
        17 ^ (1000 * literalRhinMultiplicity 3 n) *
        263 ^ (1000 * literalRhinMultiplicity 4 n) *
        271 ^ (1000 * literalRhinMultiplicity 5 n) := by
          simp only [mul_pow, ← pow_mul, Nat.mul_comm]
    _ ≤ 4 ^ (705 * n) * 3 ^ (553 * n) * 5 ^ (448 * n) *
        17 ^ (110 * n) * 263 ^ (39 * n) * 271 ^ (55 * n) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul hp1 hp2) hp3) hp4) hp5) hp6
    _ = (4 ^ 705 * 3 ^ 553 * 5 ^ 448 * 17 ^ 110 * 263 ^ 39 * 271 ^ 55) ^ n := by
      simp only [mul_pow, pow_mul]
    _ ≤ (24 ^ 1000) ^ n :=
      Nat.pow_le_pow_left literalRhinRoundedCoefficientCertificate n
    _ = (24 ^ n) ^ 1000 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The exact product of the six positive-companion coefficient sums is at
most `24^n` for every natural index. -/
theorem literalRhinCoefficientProduct_le (n : ℕ) :
    literalRhinCoefficientProduct n ≤ 24 ^ n := by
  simpa [literalRhinCoefficientProduct, Fin.prod_univ_succ, mul_assoc] using
    literalRhinRawCoefficientProduct_le_explicit n

/-- Uniform base-`24` bound for every coefficient of the literal square. -/
theorem literalRhinSquare_coeff_natAbs_le (n k : ℕ) :
    Int.natAbs ((literalRhinPolynomial n ^ 2).coeff k) ≤
      (((12 : ℕ) ^ 7 * 24 ^ n) ^ 2) := by
  calc
    Int.natAbs ((literalRhinPolynomial n ^ 2).coeff k) ≤
        (((12 : ℕ) ^ 7 * literalRhinCoefficientProduct n) ^ 2) :=
      literalRhinSquare_coeff_natAbs_le_raw n k
    _ ≤ (((12 : ℕ) ^ 7 * 24 ^ n) ^ 2) :=
      Nat.pow_le_pow_left
        (Nat.mul_le_mul_left ((12 : ℕ) ^ 7)
          (literalRhinCoefficientProduct_le n)) 2

end

end Rhin
end NumberTheory
end Erdos1135
