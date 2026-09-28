import FinitePatternCoalescence
import ProgressionConvergenceSpecialization

set_option autoImplicit false

namespace CollatzPositiveProgression

theorem every_finite_pattern_has_equal_first_hitting_times
    (F : Finset ℕ) (lower : ℕ) :
    ∃ x H R : ℕ, lower < x ∧ 1 < x ∧ ∀ n ∈ F,
      iterate H (x + n) = 1 ∧ oddCount H (x + n) = R ∧
      ∀ j < H, 1 < iterate j (x + n) := by
  let G := insert 0 (insert 1 F)
  obtain ⟨K, R, a, b, ha, _, hcert⟩ := every_finite_pattern_coalesces G
  have hbase : ∀ n ∈ G, iterate K (a + n) = b ∧ oddCount K (a + n) = R := by
    intro n hn
    simpa only [Nat.mul_zero, Nat.add_zero] using hcert n hn 0
  have hzero := hbase 0 (by simp [G])
  have hone := hbase 1 (by simp [G])
  have hunit : b % 3 ≠ 0 :=
    coalescing_distinct_equal_count_endpoint_unit K a b 0 1 R (by omega)
      hzero.1 hone.1 hzero.2 hone.2
  obtain ⟨s, t, hbound, ht, hall⟩ :=
    common_progression_has_equal_first_hitting_times G K R a b (lower + 1) hunit hbase
  have hp : 0 < 2 ^ K := by positivity
  refine ⟨a + 2 ^ K * t, K + s, R, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · intro n hn
    exact hall n (by simp [G, hn])

theorem arbitrarily_long_consecutive_equal_first_hitting_times
    (length lower : ℕ) :
    ∃ x H R : ℕ, lower < x ∧ 1 < x ∧ ∀ n < length,
      iterate H (x + n) = 1 ∧ oddCount H (x + n) = R ∧
      ∀ j < H, 1 < iterate j (x + n) := by
  obtain ⟨x, H, R, hx, hx1, h⟩ :=
    every_finite_pattern_has_equal_first_hitting_times (Finset.range length) lower
  exact ⟨x, H, R, hx, hx1, fun n hn => h n (Finset.mem_range.mpr hn)⟩

#print axioms every_finite_pattern_has_equal_first_hitting_times
#print axioms arbitrarily_long_consecutive_equal_first_hitting_times

end CollatzPositiveProgression
