import ArithmeticCylinderLaw
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem validBlock_modEq {a N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (he : Nat.ModEq 3 N M) : ValidBlock a N ↔ ValidBlock a M := by
  have hpN : 1 ≤ 2 ^ a * N := Nat.succ_le_iff.mpr (by positivity)
  have hpM : 1 ≤ 2 ^ a * M := Nat.succ_le_iff.mpr (by positivity)
  have hd := Nat.ModEq.sub_right hpN hpM (he.mul_left (2 ^ a))
  have he' : (2 ^ a * N - 1) % 3 = (2 ^ a * M - 1) % 3 := hd
  simp only [ValidBlock, Nat.dvd_iff_mod_eq_zero]
  rw [he']

theorem inverse_modEq {a N M k : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hVN : ValidBlock a N) (hVM : ValidBlock a M)
    (he : Nat.ModEq (3 ^ (k + 1)) N M) :
    Nat.ModEq (3 ^ k) (inverseValue a N) (inverseValue a M) := by
  have hm := he.mul_left (2 ^ a)
  rw [← inverse_identity hN hVN, ← inverse_identity hM hVM] at hm
  have hc := Nat.ModEq.add_right_cancel' 1 hm
  rw [pow_succ'] at hc
  exact Nat.ModEq.mul_left_cancel' (by decide : 3 ≠ 0) hc

theorem validTuple_modEq {as : List ℕ} {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (he : Nat.ModEq (3 ^ as.length) N M) :
    ValidTuple N as ↔ ValidTuple M as := by
  induction as generalizing N M with
  | nil => simp [ValidTuple]
  | cons a as ih =>
    have hm3 : Nat.ModEq 3 N M := by
      apply he.of_dvd
      simp only [List.length_cons, pow_succ]
      exact dvd_mul_left 3 (3 ^ as.length)
    have hv := validBlock_modEq (a := a) hN hM hm3
    constructor
    · rintro ⟨hVN, htail⟩
      have hVM := hv.mp hVN
      exact ⟨hVM, (ih (inverse_positive hN hVN) (inverse_positive hM hVM)
        (inverse_modEq hN hM hVN hVM he)).mp htail⟩
    · rintro ⟨hVM, htail⟩
      have hVN := hv.mpr hVM
      exact ⟨hVN, (ih (inverse_positive hN hVN) (inverse_positive hM hVM)
        (inverse_modEq hN hM hVN hVM he)).mpr htail⟩

theorem validWord_modEq {k N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (he : Nat.ModEq (3 ^ k) N M) (w : GeometricWord k) :
    ValidWord k N w ↔ ValidWord k M w := by
  apply validTuple_modEq hN hM
  simpa only [wordList_length] using he

theorem arithmetic_mass_modEq {k N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (he : Nat.ModEq (3 ^ k) N M) : arithmeticMass k N = arithmeticMass k M := by
  classical
  apply tsum_congr
  intro w
  simp only [arithmeticTerm, validWord_modEq hN hM he w]

#print axioms validTuple_modEq
#print axioms arithmetic_mass_modEq

end CollatzCylinderPacking.Arithmetic
