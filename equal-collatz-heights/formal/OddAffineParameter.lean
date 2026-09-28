import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace CollatzOddAffineParameter

theorem exists_large_odd_affine_parameter_modEq
    (a c q target lower : ℕ) (hc : c % 2 = 1) :
    ∃ t : ℕ, lower ≤ t ∧ Nat.ModEq (2 ^ q) (a + c * t) target := by
  have hcpos : 0 < c := by omega
  have hmpos : 0 < (2 : ℕ) ^ q := pow_pos (by omega) q
  have hcop : Nat.Coprime c (2 ^ q) :=
    (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hc)).pow_right q
  let z := (Nat.chineseRemainder hcop a target).val
  have hzc : Nat.ModEq c z a := (Nat.chineseRemainder hcop a target).property.1
  have hzm : Nat.ModEq (2 ^ q) z target :=
    (Nat.chineseRemainder hcop a target).property.2
  let z' := z + c * (2 ^ q * a)
  have hprod : 1 ≤ c * 2 ^ q := Nat.succ_le_of_lt (Nat.mul_pos hcpos hmpos)
  have haz : a ≤ z' := by
    have h := Nat.mul_le_mul_right a hprod
    dsimp [z']
    nlinarith
  have hzc' : Nat.ModEq c z' a := by
    simpa [z', Nat.ModEq, Nat.add_mod] using hzc
  have hzm' : Nat.ModEq (2 ^ q) z' target := by
    simpa [z', Nat.ModEq, Nat.add_mod, Nat.mul_mod] using hzm
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add haz).mp hzc'.symm
  rw [ht] at hzm'
  refine ⟨t + 2 ^ q * lower, ?_, ?_⟩
  · have h := Nat.mul_le_mul_right lower (Nat.succ_le_of_lt hmpos)
    omega
  · simpa [Nat.ModEq, Nat.mul_add, Nat.add_assoc, Nat.add_mod, Nat.mul_mod] using hzm'

theorem exists_large_odd_affine_parameter
    (a c q target lower : ℕ) (hc : c % 2 = 1) :
    ∃ t : ℕ, lower ≤ t ∧ (a + c * t) % 2 ^ q = target % 2 ^ q :=
  exists_large_odd_affine_parameter_modEq a c q target lower hc

#print axioms exists_large_odd_affine_parameter

end CollatzOddAffineParameter
