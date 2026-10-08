/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Division
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Terras/Everett Core Maps

This module starts the independent Terras/Everett theorem stack.  It records the standard,
accelerated, and odd-only Collatz maps with small branch equations for the accelerated map.
-/

namespace Erdos1135SecondScale
namespace Terras

/-- The standard Collatz map, re-exported under the Terras/Everett stack. -/
abbrev standard : ℕ → ℕ :=
  collatzStep

/-- The accelerated Collatz map that divides by one factor of two on every branch. -/
def accelerated (n : ℕ) : ℕ :=
  if Even n then n / 2 else (3 * n + 1) / 2

/-- The exponent of two in `n`, using Mathlib's prime factorization convention. -/
def twoAdicExponent (n : ℕ) : ℕ :=
  n.factorization 2

/-- The odd-only Collatz map, intended for odd inputs. -/
def oddOnly (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ twoAdicExponent (3 * n + 1)

lemma accelerated_eq_div_two_of_even {n : ℕ} (hn : Even n) :
    accelerated n = n / 2 := by
  simp [accelerated, hn]

lemma accelerated_eq_three_mul_add_one_div_two_of_not_even {n : ℕ} (hn : ¬ Even n) :
    accelerated n = (3 * n + 1) / 2 := by
  simp [accelerated, hn]

lemma accelerated_eq_standard_of_even {n : ℕ} (hn : Even n) :
    accelerated n = standard n := by
  rw [accelerated_eq_div_two_of_even hn]
  change n / 2 = collatzStep n
  rw [collatzStep_eq_div_two_of_even hn]

lemma standard_eq_two_mul_accelerated_of_not_even {n : ℕ} (hn : ¬ Even n) :
    standard n = 2 * accelerated n := by
  have hodd : Odd n := Nat.not_even_iff_odd.mp hn
  have hnum_even : Even (3 * n + 1) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨3 * k + 2, ?_⟩
    omega
  change collatzStep n = 2 * accelerated n
  rw [collatzStep_eq_three_mul_add_one_of_not_even hn]
  rw [accelerated_eq_three_mul_add_one_div_two_of_not_even hn]
  exact (two_mul_div_two_of_even hnum_even).symm

lemma two_mul_accelerated_eq_of_even {n : ℕ} (hn : Even n) :
    2 * accelerated n = n := by
  rw [accelerated_eq_div_two_of_even hn]
  exact two_mul_div_two_of_even hn

lemma two_mul_accelerated_eq_of_not_even {n : ℕ} (hn : ¬ Even n) :
    2 * accelerated n = 3 * n + 1 := by
  have hodd : Odd n := Nat.not_even_iff_odd.mp hn
  have hnum_even : Even (3 * n + 1) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨3 * k + 2, ?_⟩
    omega
  rw [accelerated_eq_three_mul_add_one_div_two_of_not_even hn]
  exact two_mul_div_two_of_even hnum_even

end Terras
end Erdos1135SecondScale
