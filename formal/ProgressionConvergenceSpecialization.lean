import CollatzAffineProgressions
import PowerTwoModuloThree
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace CollatzPositiveProgression

theorem iterate_two_pow_mul (k n : ℕ) :
    iterate k (2 ^ k * n) = n ∧ oddCount k (2 ^ k * n) = 0 := by
  induction k with
  | zero => simp [iterate, oddCount]
  | succ k ih =>
    have heq : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by rw [pow_succ]; ring
    rw [heq]
    simp only [iterate, oddCount, step_double, Nat.mul_mod_right, zero_add, ih]
    constructor <;> trivial

theorem iterate_power_two_prefix (j s : ℕ) (hj : j ≤ s) :
    iterate j (2 ^ s) = 2 ^ (s - j) := by
  have heq : 2 ^ s = 2 ^ j * 2 ^ (s - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [heq]
  exact (iterate_two_pow_mul j (2 ^ (s - j))).1

theorem iterate_prefix_gt_one (K j a t : ℕ) (hj : j < K) (ht : 0 < t) :
    1 < iterate j (a + 2 ^ K * t) := by
  have heq : a + 2 ^ K * t = a + 2 ^ j * (2 ^ (K - j) * t) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hj)]
  rw [heq, iterate_progression]
  have hp : 0 < 3 ^ oddCount j a := by positivity
  have hpow : 2 ≤ 2 ^ (K - j) := by
    have h := Nat.lt_two_pow_self (n := K - j)
    omega
  have hprod : 2 ≤ 2 ^ (K - j) * t := by nlinarith
  have hscaled := Nat.mul_le_mul_right (2 ^ (K - j) * t)
    (show 1 ≤ 3 ^ oddCount j a by omega)
  simp only [one_mul] at hscaled
  omega

theorem step_three_divisible (a : ℕ) (ha : step a % 3 = 0) :
    a % 2 = 0 ∧ a % 3 = 0 := by
  simp only [step] at ha
  split_ifs at ha <;> omega

theorem iterate_three_divisible (k a : ℕ) (ha : iterate k a % 3 = 0) :
    a % 3 = 0 ∧ oddCount k a = 0 := by
  induction k generalizing a with
  | zero => exact ⟨ha, rfl⟩
  | succ k ih =>
    obtain ⟨hstep, hcount⟩ := ih (step a) ha
    obtain ⟨heven, hthree⟩ := step_three_divisible a hstep
    exact ⟨hthree, by simp only [oddCount, heven, hcount, Nat.add_zero]⟩

theorem oddCount_zero_input (k a : ℕ) (ha : oddCount k a = 0) :
    a = 2 ^ k * iterate k a := by
  induction k generalizing a with
  | zero => simp [iterate]
  | succ k ih =>
    have heven : a % 2 = 0 := by simp only [oddCount] at ha; omega
    have hcount : oddCount k (step a) = 0 := by simp only [oddCount] at ha; omega
    have hchild := ih (step a) hcount
    have hstep : 2 * step a = a := by simp only [step, heven, if_pos]; omega
    simp only [iterate, pow_succ]
    nlinarith

theorem coalescing_distinct_equal_count_endpoint_unit
    (k a b x y r : ℕ) (hxy : x ≠ y)
    (hx : iterate k (a + x) = b) (hy : iterate k (a + y) = b)
    (hcx : oddCount k (a + x) = r) (hcy : oddCount k (a + y) = r) :
    b % 3 ≠ 0 := by
  intro hthree
  have hz := (iterate_three_divisible k (a + x) (by rw [hx]; exact hthree)).2
  have hr : r = 0 := by omega
  have hx0 := oddCount_zero_input k (a + x) hz
  have hy0 := oddCount_zero_input k (a + y) (by omega)
  rw [hx] at hx0
  rw [hy] at hy0
  omega

theorem common_progression_has_equal_first_hitting_times
    (F : Finset ℕ) (K R a b lower : ℕ)
    (hb : b % 3 ≠ 0)
    (hcert : ∀ n ∈ F, iterate K (a + n) = b ∧ oddCount K (a + n) = R) :
    ∃ s t : ℕ, lower ≤ t ∧ 0 < t ∧ ∀ n ∈ F,
      iterate (K + s) (a + 2 ^ K * t + n) = 1 ∧
      oddCount (K + s) (a + 2 ^ K * t + n) = R ∧
      ∀ j < K + s, 1 < iterate j (a + 2 ^ K * t + n) := by
  obtain ⟨s, t, ht, hpower⟩ :=
    CollatzPowerTwo.power_two_in_every_unit_progression R b (lower + 1) hb
  refine ⟨s, t, by omega, by omega, ?_⟩
  intro n hn
  obtain ⟨hi, ho⟩ := hcert n hn
  have hbase : a + 2 ^ K * t + n = (a + n) + 2 ^ K * t := by omega
  have hmeet : iterate K (a + 2 ^ K * t + n) = 2 ^ s := by
    rw [hbase, iterate_progression, hi, ho]
    exact hpower
  have hcount : oddCount K (a + 2 ^ K * t + n) = R := by
    rw [hbase, oddCount_progression, ho]
  obtain ⟨hend, heven⟩ := iterate_two_pow_mul s 1
  simp only [mul_one] at hend heven
  refine ⟨?_, ?_, ?_⟩
  · rw [iterate_add, hmeet, hend]
  · rw [oddCount_add, hcount, hmeet, heven, Nat.add_zero]
  · intro j hj
    by_cases hprefix : j < K
    · rw [hbase]
      exact iterate_prefix_gt_one K j (a + n) t hprefix (by omega)
    · have hsplit : j = K + (j - K) := by omega
      have hle : j - K ≤ s := by omega
      rw [hsplit, iterate_add, hmeet, iterate_power_two_prefix (j - K) s hle]
      have hp := Nat.lt_two_pow_self (n := s - (j - K))
      omega

#print axioms common_progression_has_equal_first_hitting_times

end CollatzPositiveProgression
