import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace CollatzPowerTwo

theorem four_power_lift (n : ℕ) :
    ∃ c : ℕ, 4 ^ (3 ^ n) = 1 + 3 ^ (n + 1) * (1 + 3 * c) := by
  induction n with
  | zero => exact ⟨0, by norm_num⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + 3 ^ n * (1 + 3 * c) ^ 2 + (3 ^ n) ^ 2 * (1 + 3 * c) ^ 3, ?_⟩
    rw [pow_succ (3 : ℕ) n, pow_mul, hc]
    simp only [pow_succ]
    ring

theorem three_residue_choice (a q : ℤ) (ha : a % 3 ≠ 0) :
    ∃ j : ℕ, j ≤ 2 ∧ (a * j - q) % 3 = 0 := by
  have ha3 : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases ha3 with ha3 | ha3 <;> rcases hq3 with hq3 | hq3 | hq3
  all_goals first
    | exact ⟨0, by omega, by omega⟩
    | exact ⟨1, by omega, by omega⟩
    | exact ⟨2, by omega, by omega⟩

theorem lift_residue (a b m : ℕ) (hm : 3 ∣ m) (ha : a % 3 ≠ 0)
    (hab : a ≡ b [MOD m]) :
    ∃ j : ℕ, j ≤ 2 ∧ a * (1 + m) ^ j ≡ b [MOD 3 * m] := by
  obtain ⟨d, hd⟩ := hm
  obtain ⟨q, hq⟩ := hab.dvd
  have haz : (a : ℤ) % 3 ≠ 0 := by exact_mod_cast ha
  obtain ⟨j, hj, hmod⟩ := three_residue_choice a q haz
  obtain ⟨e, he⟩ := Int.dvd_of_emod_eq_zero hmod
  refine ⟨j, hj, Nat.modEq_of_dvd ?_⟩
  have hmz : (m : ℤ) = 3 * d := by exact_mod_cast hd
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · refine ⟨-e, ?_⟩
    push_cast at *
    norm_num at he ⊢
    nlinarith [hq]
  · refine ⟨-e, ?_⟩
    push_cast at *
    norm_num at he ⊢
    nlinarith [hq]
  · refine ⟨-(e + (a : ℤ) * d), ?_⟩
    push_cast at *
    norm_num at he ⊢
    have hbase : (b : ℤ) = a + (m : ℤ) * q := by omega
    have hquot : q = (a : ℤ) * 2 - 3 * e := by omega
    rw [hbase, hquot, hmz]
    ring

theorem four_power_mod (n : ℕ) :
    4 ^ (3 ^ n) ≡ 1 + 3 ^ (n + 1) [MOD 3 * 3 ^ (n + 1)] := by
  obtain ⟨c, hc⟩ := four_power_lift n
  rw [hc]
  have heq : 1 + 3 ^ (n + 1) * (1 + 3 * c) =
      (3 * 3 ^ (n + 1)) * c + (1 + 3 ^ (n + 1)) := by ring
  rw [heq]
  exact Nat.ModEq.modulus_mul_add

theorem exists_two_power_mod_successor (n b : ℕ) (hb : b % 3 ≠ 0) :
    ∃ s : ℕ, 2 ^ s ≡ b [MOD 3 ^ (n + 1)] := by
  induction n with
  | zero =>
    have h : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases h with h | h
    · exact ⟨0, by simpa [Nat.ModEq] using h.symm⟩
    · exact ⟨1, by simpa [Nat.ModEq] using h.symm⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    have hdiv : 3 ∣ 3 ^ (n + 1) := by exact dvd_pow_self 3 (by omega)
    have ha : (2 ^ s) % 3 ≠ 0 := by
      have h := hs.of_dvd hdiv
      change (2 ^ s) % 3 = b % 3 at h
      omega
    obtain ⟨j, _, hj⟩ := lift_residue (2 ^ s) b (3 ^ (n + 1)) hdiv ha hs
    refine ⟨s + (2 * 3 ^ n) * j, ?_⟩
    have hpow := (four_power_mod n).pow j
    have hmul := hpow.mul_left (2 ^ s)
    have heq : (2 : ℕ) ^ (s + (2 * 3 ^ n) * j) =
        2 ^ s * (4 ^ (3 ^ n)) ^ j := by
      rw [pow_add, pow_mul, pow_mul]
      norm_num
    rw [heq, pow_succ]
    simpa [Nat.mul_comm] using hmul.trans hj

theorem exists_two_power_mod (n b : ℕ) (hb : b % 3 ≠ 0) :
    ∃ s : ℕ, 2 ^ s ≡ b [MOD 3 ^ n] := by
  cases n with
  | zero => exact ⟨0, by simp [Nat.ModEq]; omega⟩
  | succ n => exact exists_two_power_mod_successor n b hb

theorem two_power_period (n : ℕ) :
    2 ^ (2 * 3 ^ n) ≡ 1 [MOD 3 ^ n] := by
  obtain ⟨c, hc⟩ := four_power_lift n
  rw [pow_mul]
  norm_num only [show (2 : ℕ) ^ 2 = 4 by norm_num]
  rw [hc, pow_succ]
  have heq : 1 + 3 ^ n * 3 * (1 + 3 * c) =
      3 ^ n * (3 * (1 + 3 * c)) + 1 := by ring
  rw [heq]
  exact Nat.ModEq.modulus_mul_add

theorem exists_large_two_power_mod (n b bound : ℕ) (hb : b % 3 ≠ 0) :
    ∃ s : ℕ, bound ≤ s ∧ 2 ^ s ≡ b [MOD 3 ^ n] := by
  obtain ⟨s, hs⟩ := exists_two_power_mod n b hb
  refine ⟨s + (2 * 3 ^ n) * bound, ?_, ?_⟩
  · have hp : 0 < 3 ^ n := by positivity
    nlinarith
  · have hperiod := (two_power_period n).pow bound
    have hmul := hs.mul hperiod
    simpa only [pow_add, pow_mul, one_pow, mul_one] using hmul

theorem power_two_in_every_unit_progression (n b bound : ℕ) (hb : b % 3 ≠ 0) :
    ∃ s t : ℕ, bound ≤ t ∧ b + 3 ^ n * t = 2 ^ s := by
  obtain ⟨s, hbound, hs⟩ := exists_large_two_power_mod n b (b + 3 ^ n * bound) hb
  have hbig : b + 3 ^ n * bound ≤ 2 ^ s :=
    le_trans hbound (Nat.le_of_lt (Nat.lt_two_pow_self (n := s)))
  have hb_le : b ≤ 2 ^ s := by omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hb_le).mp hs.symm
  refine ⟨s, t, ?_, ?_⟩
  · have hp : 0 < 3 ^ n := by positivity
    have heq : 2 ^ s = b + 3 ^ n * t := by omega
    nlinarith
  · omega

#print axioms exists_two_power_mod
#print axioms power_two_in_every_unit_progression

end CollatzPowerTwo
