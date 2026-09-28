/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Parity

/-!
# Residue-Class Lemmas

This module is for modular arithmetic and residue-class descriptions of Collatz behavior.
-/

namespace Erdos1135SecondScale

lemma nat_modEq_self_mod (m n : ℕ) :
    Nat.ModEq m n (n % m) :=
  (Nat.mod_modEq n m).symm

lemma nat_modEq_mod_self (m n : ℕ) :
    Nat.ModEq m (n % m) n :=
  Nat.mod_modEq n m

lemma nat_modEq_zero_of_dvd {m n : ℕ} (h : m ∣ n) :
    Nat.ModEq m n 0 :=
  Nat.modEq_zero_iff_dvd.mpr h

lemma nat_dvd_of_modEq_zero {m n : ℕ} (h : Nat.ModEq m n 0) :
    m ∣ n :=
  Nat.modEq_zero_iff_dvd.mp h

lemma nat_modEq_three_mul_add_one {m a b : ℕ} (h : Nat.ModEq m a b) :
    Nat.ModEq m (3 * a + 1) (3 * b + 1) :=
  ((Nat.ModEq.refl 3).mul h).add (Nat.ModEq.refl 1)

lemma nat_modEq_mul_left_modulus {a m n r : ℕ} (h : Nat.ModEq m n r) :
    Nat.ModEq (a * m) (a * n) (a * r) := by
  rw [Nat.ModEq] at h ⊢
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  exact congrArg (fun t => a * t) h

lemma nat_modEq_div_two_of_modEq_mul_two_of_two_dvd {m n r : ℕ}
    (hn : 2 ∣ n) (hr : 2 ∣ r) (h : Nat.ModEq (2 * m) n r) :
    Nat.ModEq m (n / 2) (r / 2) := by
  rcases hn with ⟨a, rfl⟩
  rcases hr with ⟨b, rfl⟩
  by_cases hm : m = 0
  · subst m
    simpa using h
  · have hraw : Nat.ModEq ((2 * m) / Nat.gcd (2 * m) 2) a b := by
      exact Nat.ModEq.cancel_left_div_gcd (by omega) h
    have hmod : (2 * m) / Nat.gcd (2 * m) 2 = m := by
      have hgcd : Nat.gcd (2 * m) 2 = 2 := by
        rw [Nat.gcd_comm]
        exact Nat.gcd_eq_left (by omega)
      rw [hgcd]
      exact Nat.mul_div_right m (by norm_num : 0 < 2)
    simpa [hmod, Nat.mul_div_right] using hraw

lemma collatzStep_modEq_three_mul_add_one_of_not_even {m n r : ℕ}
    (hn : ¬ Even n) (h : Nat.ModEq m n r) :
    Nat.ModEq m (collatzStep n) (3 * r + 1) := by
  rw [collatzStep_eq_three_mul_add_one_of_not_even hn]
  exact nat_modEq_three_mul_add_one h

lemma collatzStep_modEq_three_mul_add_one_of_odd {m n r : ℕ}
    (hn : Odd n) (h : Nat.ModEq m n r) :
    Nat.ModEq m (collatzStep n) (3 * r + 1) :=
  collatzStep_modEq_three_mul_add_one_of_not_even (Nat.not_even_iff_odd.mpr hn) h

lemma collatzStep_modEq_three_mul_add_one_of_mod_two_eq_one {m n r : ℕ}
    (hn : n % 2 = 1) (h : Nat.ModEq m n r) :
    Nat.ModEq m (collatzStep n) (3 * r + 1) :=
  collatzStep_modEq_three_mul_add_one_of_not_even (Nat.not_even_iff.mpr hn) h

lemma collatzStep_modEq_div_two_of_even_of_modEq_mul_two {m n r : ℕ}
    (hn : Even n) (hr : 2 ∣ r) (h : Nat.ModEq (2 * m) n r) :
    Nat.ModEq m (collatzStep n) (r / 2) := by
  rw [collatzStep_eq_div_two_of_even hn]
  exact nat_modEq_div_two_of_modEq_mul_two_of_two_dvd (Even.two_dvd hn) hr h

end Erdos1135SecondScale
