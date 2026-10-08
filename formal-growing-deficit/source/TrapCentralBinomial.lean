import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-! An elementary polynomial lower bound for the central geometric-sum mass. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_centralBinom_eq_twice_odd_choose (k : ℕ) (hk : 1 ≤ k) :
    Nat.centralBinom k = 2 * (2 * k - 1).choose (k - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.centralBinom_eq_two_mul_choose]
  have he : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [he, Nat.choose_succ_succ, Nat.choose_symm_half]
  simp only [Nat.succ_sub_one, two_mul]

theorem trap_central_geometric_mass_lower (k : ℕ) (hk : 1 ≤ k) :
    1 / (4 * (k : ℝ)) ≤
      ((2 * k - 1).choose (k - 1) : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by
  have hnat := Nat.four_pow_le_two_mul_self_mul_centralBinom k (by omega)
  rw [trap_centralBinom_eq_twice_odd_choose k hk] at hnat
  have hreal : (4 : ℝ) ^ k ≤
      4 * (k : ℝ) * ((2 * k - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast (show 4 ^ k ≤ 4 * k * (2 * k - 1).choose (k - 1) by
      nlinarith [hnat])
  have hpow : (1 / 2 : ℝ) ^ (2 * k) = 1 / (4 : ℝ) ^ k := by
    rw [pow_mul, div_pow]
    norm_num [div_pow]
  rw [hpow, mul_one_div]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    (by simpa [mul_comm] using hreal)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_central_geometric_mass_lower
