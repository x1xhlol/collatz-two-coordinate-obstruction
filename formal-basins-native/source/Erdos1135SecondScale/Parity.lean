/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.CollatzStep

/-!
# Parity Lemmas

Parity-specific Collatz facts belong here. The initial seed lemmas live in
`Erdos1135SecondScale.CollatzStep`; this module is reserved for larger parity families.
-/

namespace Erdos1135SecondScale

lemma nat_even_iff_two_dvd {n : ℕ} :
    Even n ↔ 2 ∣ n :=
  even_iff_two_dvd

lemma nat_even_iff_mod_two_eq_zero {n : ℕ} :
    Even n ↔ n % 2 = 0 :=
  Nat.even_iff

lemma nat_not_even_iff_mod_two_eq_one {n : ℕ} :
    ¬ Even n ↔ n % 2 = 1 :=
  Nat.not_even_iff

lemma nat_not_even_iff_odd {n : ℕ} :
    ¬ Even n ↔ Odd n :=
  Nat.not_even_iff_odd

lemma nat_odd_iff_mod_two_eq_one {n : ℕ} :
    Odd n ↔ n % 2 = 1 :=
  Nat.odd_iff

lemma collatzStep_eq_div_two_of_two_dvd {n : ℕ} (hn : 2 ∣ n) :
    collatzStep n = n / 2 :=
  collatzStep_eq_div_two_of_even (even_iff_two_dvd.mpr hn)

lemma collatzStep_eq_div_two_of_mod_two_eq_zero {n : ℕ} (hn : n % 2 = 0) :
    collatzStep n = n / 2 :=
  collatzStep_eq_div_two_of_even (Nat.even_iff.mpr hn)

lemma collatzStep_eq_three_mul_add_one_of_odd {n : ℕ} (hn : Odd n) :
    collatzStep n = 3 * n + 1 :=
  collatzStep_eq_three_mul_add_one_of_not_even (Nat.not_even_iff_odd.mpr hn)

lemma collatzStep_eq_three_mul_add_one_of_not_two_dvd {n : ℕ} (hn : ¬ 2 ∣ n) :
    collatzStep n = 3 * n + 1 :=
  collatzStep_eq_three_mul_add_one_of_not_even (by
    intro he
    exact hn (Even.two_dvd he))

lemma collatzStep_eq_three_mul_add_one_of_mod_two_eq_one {n : ℕ} (hn : n % 2 = 1) :
    collatzStep n = 3 * n + 1 :=
  collatzStep_eq_three_mul_add_one_of_not_even (Nat.not_even_iff.mpr hn)

lemma collatzStep_eq_if_mod_two (n : ℕ) :
    collatzStep n = if n % 2 = 0 then n / 2 else 3 * n + 1 := by
  by_cases h : n % 2 = 0
  · have he : Even n := Nat.even_iff.mpr h
    simp [collatzStep, CollatzConjecture.collatzStep, he, h]
  · have hne : ¬ Even n := by
      intro he
      exact h (Nat.even_iff.mp he)
    simp [collatzStep, CollatzConjecture.collatzStep, hne, h]

end Erdos1135SecondScale
