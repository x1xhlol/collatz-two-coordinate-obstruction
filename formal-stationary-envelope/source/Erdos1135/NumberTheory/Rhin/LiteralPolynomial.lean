import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FinCases

/-!
# Rhin's literal p. 162 polynomial

This file transcribes the six factors and fixed prefactor printed by Rhin on
p. 162.  The paper displays each weight to six decimal places.  For the G8a
formalization, `literalRhinWeightNumerator` records those displayed digits as
an exact millionth and `literalRhinMultiplicity` takes the resulting natural
floor.  This is an explicit exact reading of the displayed data, not a claim
that the source supplied hidden higher-precision rational parameters.

Indices `0,...,5` correspond respectively to the printed factors
`Q₁,...,Q₆`.  In particular, the source has the fixed scalar `12⁷` and
`Q₆ = 19*X² - 108*X + 144`.  This module intentionally follows Rhin's
`-108`; Wu's later `-104` variant is a different polynomial and is not covered
by the certificates derived from these definitions.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

open Polynomial
open scoped BigOperators

/-- Rhin p. 162: `Q₁ = X - 3`. -/
def literalRhinFactor1 : ℤ[X] :=
  X - C 3

/-- Rhin p. 162: `Q₂ = X - 2`. -/
def literalRhinFactor2 : ℤ[X] :=
  X - C 2

/-- Rhin p. 162: `Q₃ = X - 4`. -/
def literalRhinFactor3 : ℤ[X] :=
  X - C 4

/-- Rhin p. 162: `Q₄ = 5*X - 12`. -/
def literalRhinFactor4 : ℤ[X] :=
  C 5 * X - C 12

/-- Rhin p. 162: `Q₅ = 17*X² - 102*X + 144`. -/
def literalRhinFactor5 : ℤ[X] :=
  C 17 * X ^ 2 - C 102 * X + C 144

/-- Rhin p. 162: `Q₆ = 19*X² - 108*X + 144`. -/
def literalRhinFactor6 : ℤ[X] :=
  C 19 * X ^ 2 - C 108 * X + C 144

/-- The six p. 162 factors, indexed in the printed order `Q₁,...,Q₆`. -/
def literalRhinFactor : Fin 6 → ℤ[X] :=
  ![literalRhinFactor1, literalRhinFactor2, literalRhinFactor3,
    literalRhinFactor4, literalRhinFactor5, literalRhinFactor6]

/-- The degrees `1,1,1,1,2,2` of the six printed factors. -/
def literalRhinFactorDegree : Fin 6 → ℕ :=
  ![1, 1, 1, 1, 2, 2]

/-- The exact millionth numerators read from the six displayed p. 162
weights. -/
def literalRhinWeightNumerator : Fin 6 → ℕ :=
  ![704324, 552418, 447582, 109072, 38934, 54368]

/-- The source exponent `[bᵢ*n]`, using the exact-millionth reading of the
displayed six-decimal weight. -/
def literalRhinMultiplicity (i : Fin 6) (n : ℕ) : ℕ :=
  literalRhinWeightNumerator i * n / 1000000

/-- The weighted degree order contributed by the six floored factor powers. -/
def literalRhinDegreeOrder (n : ℕ) : ℕ :=
  ∑ i : Fin 6,
    literalRhinMultiplicity i n * literalRhinFactorDegree i

/-- The literal p. 162 polynomial, with the source's fixed prefactor `12⁷`. -/
def literalRhinPolynomial (n : ℕ) : ℤ[X] :=
  C ((12 : ℤ) ^ 7) *
    ∏ i : Fin 6, literalRhinFactor i ^ literalRhinMultiplicity i n

private theorem natDegree_X_sub_C_le_one (c : ℤ) :
    (X - C c : ℤ[X]).natDegree ≤ 1 := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  simp

private theorem natDegree_C_mul_X_sub_C_le_one (a c : ℤ) :
    (C a * X - C c : ℤ[X]).natDegree ≤ 1 := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · apply le_trans Polynomial.natDegree_mul_le
    simp
  · simp

private theorem natDegree_quadratic_le_two (a b c : ℤ) :
    (C a * X ^ 2 - C b * X + C c : ℤ[X]).natDegree ≤ 2 := by
  apply le_trans (Polynomial.natDegree_add_le _ _)
  apply max_le
  · apply le_trans (Polynomial.natDegree_sub_le _ _)
    apply max_le
    · apply le_trans Polynomial.natDegree_mul_le
      simp
    · apply le_trans Polynomial.natDegree_mul_le
      simp
  · simp

/-- Each p. 162 factor has at most its displayed degree. -/
theorem literalRhinFactor_natDegree_le (i : Fin 6) :
    (literalRhinFactor i).natDegree ≤ literalRhinFactorDegree i := by
  fin_cases i
  · exact natDegree_X_sub_C_le_one 3
  · exact natDegree_X_sub_C_le_one 2
  · exact natDegree_X_sub_C_le_one 4
  · exact natDegree_C_mul_X_sub_C_le_one 5 12
  · exact natDegree_quadratic_le_two 17 102 144
  · exact natDegree_quadratic_le_two 19 108 144

/-- Flooring the displayed weights cannot raise their total weighted order. -/
theorem literalRhinDegreeOrder_le_two_mul (n : ℕ) :
    literalRhinDegreeOrder n ≤ 2 * n := by
  simp [literalRhinDegreeOrder, literalRhinMultiplicity,
    literalRhinWeightNumerator, literalRhinFactorDegree, Fin.sum_univ_succ]
  omega

/-- The six floor errors lose at most seven units of weighted degree. -/
theorem literalRhinDegreeOrder_add_seven_ge (n : ℕ) :
    2 * n ≤ literalRhinDegreeOrder n + 7 := by
  simp [literalRhinDegreeOrder, literalRhinMultiplicity,
    literalRhinWeightNumerator, literalRhinFactorDegree, Fin.sum_univ_succ]
  omega

/-- The displayed p. 162 weights give the degree cap needed by the p. 159
row construction.  Floors make this an upper bound, not a degree equality. -/
theorem literalRhinPolynomial_natDegree_le (n : ℕ) :
    (literalRhinPolynomial n).natDegree ≤ 2 * n := by
  have hProd :
      (∏ i : Fin 6,
        literalRhinFactor i ^ literalRhinMultiplicity i n).natDegree ≤
        ∑ i : Fin 6,
          literalRhinMultiplicity i n * literalRhinFactorDegree i := by
    calc
      (∏ i : Fin 6,
          literalRhinFactor i ^ literalRhinMultiplicity i n).natDegree ≤
          ∑ i : Fin 6,
            (literalRhinFactor i ^ literalRhinMultiplicity i n).natDegree := by
        exact Polynomial.natDegree_prod_le Finset.univ
          (fun i : Fin 6 ↦
            literalRhinFactor i ^ literalRhinMultiplicity i n)
      _ ≤ ∑ i : Fin 6,
          literalRhinMultiplicity i n * literalRhinFactorDegree i := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_left (literalRhinMultiplicity i n)
            (literalRhinFactor_natDegree_le i))
  unfold literalRhinPolynomial
  calc
    (C ((12 : ℤ) ^ 7) *
        ∏ i : Fin 6,
          literalRhinFactor i ^ literalRhinMultiplicity i n).natDegree ≤
        (C ((12 : ℤ) ^ 7)).natDegree +
          (∏ i : Fin 6,
            literalRhinFactor i ^ literalRhinMultiplicity i n).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + ∑ i : Fin 6,
        literalRhinMultiplicity i n * literalRhinFactorDegree i := by
      exact Nat.add_le_add (by simp) hProd
    _ ≤ 2 * n := by
      simpa only [zero_add, literalRhinDegreeOrder] using
        literalRhinDegreeOrder_le_two_mul n

end

end Rhin
end NumberTheory
end Erdos1135
