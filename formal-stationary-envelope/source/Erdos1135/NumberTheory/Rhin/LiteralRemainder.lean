/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.NumberTheory.Rhin.LiteralPolynomial
import Erdos1135.NumberTheory.Rhin.RemainderCore

/-!
# Literal polynomial bridge for Rhin remainder bounds

This file connects the exact p. 162 polynomial data to its six-factor real
evaluation and to the outward thousandth exponent envelopes used by the
continuous cell certificate.  It does not duplicate the six source
multiplicities.  The active factor is Rhin's printed
`19*X^2 - 108*X + 144`; the derived remainder certificates here do not cover
Wu's later `-104` variant.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

open Polynomial
open scoped BigOperators

/-- The real evaluations of the six literal p. 162 factors, in their printed
order. -/
def literalRhinFactorReal (x : ℝ) : Fin 6 → ℝ :=
  ![x - 3, x - 2, x - 4, 5 * x - 12,
    17 * x ^ 2 - 102 * x + 144,
    19 * x ^ 2 - 108 * x + 144]

/-- Each entry of `literalRhinFactorReal` is exactly the real evaluation of
the corresponding production polynomial factor. -/
theorem literalRhinFactor_eval₂ (i : Fin 6) (x : ℝ) :
    (literalRhinFactor i).eval₂ (Int.castRingHom ℝ) x =
      literalRhinFactorReal x i := by
  fin_cases i <;>
    simp [literalRhinFactor, literalRhinFactor1, literalRhinFactor2,
      literalRhinFactor3, literalRhinFactor4, literalRhinFactor5,
      literalRhinFactor6, literalRhinFactorReal, Polynomial.eval₂_sub,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X]

/-- Real evaluation of the production literal polynomial is exactly the
fixed scalar times the product of the six real factor evaluations with the
production multiplicities. -/
theorem literalRhinPolynomial_eval₂_eq_factorProduct (n : ℕ) (x : ℝ) :
    (literalRhinPolynomial n).eval₂ (Int.castRingHom ℝ) x =
      (12 : ℝ) ^ 7 *
        ∏ i : Fin 6,
          literalRhinFactorReal x i ^ literalRhinMultiplicity i n := by
  unfold literalRhinPolynomial
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_finset_prod]
  simp only [Polynomial.eval₂_pow, literalRhinFactor_eval₂]
  norm_num

/-- Outward thousandth ceilings of the exact-millionth displayed weights.
These are certificate parameters, not a second reading of the source data. -/
def literalRhinUpperExponent : Fin 6 → ℕ :=
  ![705, 553, 448, 110, 39, 55]

/-- Outward thousandth floors of the exact-millionth displayed weights.
These are certificate parameters, not a second reading of the source data. -/
def literalRhinLowerExponent : Fin 6 → ℕ :=
  ![704, 552, 447, 109, 38, 54]

/-- The thousandth ceiling envelope dominates every production
multiplicity. -/
theorem literalRhinMultiplicity_upper (n : ℕ) (i : Fin 6) :
    1000 * literalRhinMultiplicity i n ≤
      literalRhinUpperExponent i * n := by
  fin_cases i
  · have h := Nat.div_mul_le_self (704324 * n) 1000000
    change 1000 * (704324 * n / 1000000) ≤ 705 * n
    omega
  · have h := Nat.div_mul_le_self (552418 * n) 1000000
    change 1000 * (552418 * n / 1000000) ≤ 553 * n
    omega
  · have h := Nat.div_mul_le_self (447582 * n) 1000000
    change 1000 * (447582 * n / 1000000) ≤ 448 * n
    omega
  · have h := Nat.div_mul_le_self (109072 * n) 1000000
    change 1000 * (109072 * n / 1000000) ≤ 110 * n
    omega
  · have h := Nat.div_mul_le_self (38934 * n) 1000000
    change 1000 * (38934 * n / 1000000) ≤ 39 * n
    omega
  · have h := Nat.div_mul_le_self (54368 * n) 1000000
    change 1000 * (54368 * n / 1000000) ≤ 55 * n
    omega

/-- The thousandth floor envelope is at most one rounding unit above every
production multiplicity. -/
theorem literalRhinMultiplicity_lower (n : ℕ) (i : Fin 6) :
    literalRhinLowerExponent i * n ≤
      1000 * literalRhinMultiplicity i n + 1000 := by
  fin_cases i
  · have h := Nat.mod_add_div (704324 * n) 1000000
    have hr := Nat.mod_lt (704324 * n) (by norm_num : 0 < (1000000 : ℕ))
    change 704 * n ≤ 1000 * (704324 * n / 1000000) + 1000
    omega
  · have h := Nat.mod_add_div (552418 * n) 1000000
    have hr := Nat.mod_lt (552418 * n) (by norm_num : 0 < (1000000 : ℕ))
    change 552 * n ≤ 1000 * (552418 * n / 1000000) + 1000
    omega
  · have h := Nat.mod_add_div (447582 * n) 1000000
    have hr := Nat.mod_lt (447582 * n) (by norm_num : 0 < (1000000 : ℕ))
    change 447 * n ≤ 1000 * (447582 * n / 1000000) + 1000
    omega
  · have h := Nat.mod_add_div (109072 * n) 1000000
    have hr := Nat.mod_lt (109072 * n) (by norm_num : 0 < (1000000 : ℕ))
    change 109 * n ≤ 1000 * (109072 * n / 1000000) + 1000
    omega
  · have h := Nat.mod_add_div (38934 * n) 1000000
    have hr := Nat.mod_lt (38934 * n) (by norm_num : 0 < (1000000 : ℕ))
    change 38 * n ≤ 1000 * (38934 * n / 1000000) + 1000
    omega
  · have h := Nat.mod_add_div (54368 * n) 1000000
    have hr := Nat.mod_lt (54368 * n) (by norm_num : 0 < (1000000 : ℕ))
    change 54 * n ≤ 1000 * (54368 * n / 1000000) + 1000
    omega

end

end Rhin
end NumberTheory
end Erdos1135
