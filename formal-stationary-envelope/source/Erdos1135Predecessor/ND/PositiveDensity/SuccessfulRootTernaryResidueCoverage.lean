/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.A5HistoricalAdjacentCylinderPreviousPhysicalLowerShellNoGo
import Erdos1135Predecessor.ND.PositiveDensity.TargetCounting
import Mathlib.NumberTheory.Multiplicity

namespace Erdos1135Predecessor.ND.PositiveDensity

theorem ndCollapseSource_add (m n : ℕ) :
    ndA5PreviousPhysicalCollapseSource (m + n) =
      ndA5PreviousPhysicalCollapseSource m + 4 ^ m * ndA5PreviousPhysicalCollapseSource n := by
  have ha := three_mul_ndA5PreviousPhysicalCollapseSource_add_one (m + n)
  have hm := three_mul_ndA5PreviousPhysicalCollapseSource_add_one m
  have hn := three_mul_ndA5PreviousPhysicalCollapseSource_add_one n
  rw [pow_add, ← hm, ← hn] at ha
  nlinarith

theorem threePow_succ_dvd_fourPow_sub_one_iff (q n : ℕ) :
    3 ^ (q + 1) ∣ 4 ^ n - 1 ↔ 3 ^ q ∣ n := by
  rw [pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity]
  have h := Nat.emultiplicity_pow_sub_pow
    (p := 3) (x := 4) (y := 1)
    (by norm_num : Nat.Prime 3) (by norm_num : Odd 3)
    (by norm_num : 3 ∣ 4 - 1) (by norm_num : ¬ 3 ∣ 4) n
  simp only [one_pow] at h
  rw [h]
  norm_num [Nat.Prime.emultiplicity_self (by norm_num : Nat.Prime 3)]
  rw [add_comm (1 : ENat), ENat.add_le_add_iff_right (by simp)]

theorem threePow_dvd_collapseSource_iff (q n : ℕ) :
    3 ^ q ∣ ndA5PreviousPhysicalCollapseSource n ↔ 3 ^ q ∣ n := by
  have h := three_mul_ndA5PreviousPhysicalCollapseSource_add_one n
  have he : 4 ^ n - 1 = 3 * ndA5PreviousPhysicalCollapseSource n := by omega
  have hl := threePow_succ_dvd_fourPow_sub_one_iff q n
  rw [he, pow_succ, Nat.mul_comm (3 ^ q) 3,
    Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)] at hl
  exact hl

theorem ndCollapseSource_modEq_of_add_iff (q m n : ℕ) :
    Nat.ModEq (3 ^ q) (ndA5PreviousPhysicalCollapseSource m)
      (ndA5PreviousPhysicalCollapseSource (m + n)) ↔ 3 ^ q ∣ n := by
  rw [ndCollapseSource_add, Nat.left_modEq_add_iff]
  have hc : Nat.Coprime (3 ^ q) (4 ^ m) := by
    exact (show Nat.Coprime 3 4 by norm_num).pow q m
  rw [hc.dvd_mul_left, threePow_dvd_collapseSource_iff]

theorem ndCollapseSource_residue_injective (q : ℕ) :
    Function.Injective (fun m : Fin (3 ^ q) =>
      (⟨ndA5PreviousPhysicalCollapseSource m % 3 ^ q,
        Nat.mod_lt _ (by positivity)⟩ : Fin (3 ^ q))) := by
  intro m n he
  apply Fin.ext
  have heq : Nat.ModEq (3 ^ q) (ndA5PreviousPhysicalCollapseSource m)
      (ndA5PreviousPhysicalCollapseSource n) := congrArg Fin.val he
  suffices h : ∀ (a b : Fin (3 ^ q)), a ≤ b →
      Nat.ModEq (3 ^ q) (ndA5PreviousPhysicalCollapseSource a)
        (ndA5PreviousPhysicalCollapseSource b) → (a : ℕ) = b by
    rcases le_total m n with hmn | hnm
    · exact h m n hmn heq
    · exact (h n m hnm heq.symm).symm
  intro a b hab hmod
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show (a : ℕ) ≤ b from hab)
  rw [hd] at hmod
  have hdiv := (ndCollapseSource_modEq_of_add_iff q a d).mp hmod
  have hdlt : d < 3 ^ q := by have h := b.isLt; omega
  have hz : d = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hdlt
  omega

theorem ndCollapseSource_residue_surjective (q : ℕ) :
    Function.Surjective (fun m : Fin (3 ^ q) =>
      (⟨ndA5PreviousPhysicalCollapseSource m % 3 ^ q,
        Nat.mod_lt _ (by positivity)⟩ : Fin (3 ^ q))) :=
  Finite.surjective_of_injective (ndCollapseSource_residue_injective q)

end Erdos1135Predecessor.ND.PositiveDensity
