import OddHarmonicCumulative

set_option autoImplicit false

open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open DirichletAbelian

theorem finite_reciprocal_le_harmonic_prefix (Q : Finset ℕ) (N : ℕ)
    (hQ : ∀ q ∈ Q, q ≤ N) :
    (∑ q ∈ Q, (1 : ℝ) / q) ≤ ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1 : ℕ) := by
  have hsub : Q ⊆ Finset.range (N + 1) := by
    intro q hq
    exact Finset.mem_range.mpr (by have := hQ q hq; omega)
  calc
    (∑ q ∈ Q, (1 : ℝ) / q) ≤ ∑ q ∈ Finset.range (N + 1), (1 : ℝ) / q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1 : ℕ) := by
      rw [Finset.sum_range_succ']
      simp

theorem finite_odd_reciprocal_le_odd_harmonic_prefix (Q : Finset ℕ) (N : ℕ)
    (hQ : ∀ q ∈ Q, q ≤ N) (hodd : ∀ q ∈ Q, q % 2 = 1) :
    (∑ q ∈ Q, (1 : ℝ) / q) ≤
      ∑ n ∈ Finset.range N, (if (n + 1) % 2 = 1 then (1 : ℝ) else 0) / (n + 1 : ℕ) := by
  have hsub : Q ⊆ Finset.range (N + 1) := by
    intro q hq
    exact Finset.mem_range.mpr (by have := hQ q hq; omega)
  calc
    (∑ q ∈ Q, (1 : ℝ) / q) =
        ∑ q ∈ Q, (if q % 2 = 1 then (1 : ℝ) else 0) / q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos (hodd q hq)]
    _ ≤ ∑ q ∈ Finset.range (N + 1), (if q % 2 = 1 then (1 : ℝ) else 0) / q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _ _
      split_ifs <;> positivity
    _ = ∑ n ∈ Finset.range N,
        (if (n + 1) % 2 = 1 then (1 : ℝ) else 0) / (n + 1 : ℕ) := by
      rw [Finset.sum_range_succ']
      simp

theorem finite_odd_dyadic_reciprocal_budget (Q : Finset ℕ) (K : ℕ)
    (hQ : ∀ q ∈ Q, q ≤ 2 ^ (6 * K)) (hodd : ∀ q ∈ Q, q % 2 = 1) :
    (∑ q ∈ Q, (1 : ℝ) / q) ≤ 2 + 3 * (K : ℝ) := by
  by_cases hK : K = 0
  · subst K
    have hh := finite_reciprocal_le_harmonic_prefix Q 1 (by simpa using hQ)
    norm_num at hh ⊢
    linarith
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have ht : Real.log 2 ≤ (6 * (K : ℝ)) * Real.log 2 := by
    have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    nlinarith
  have he : Real.exp ((6 * (K : ℝ)) * Real.log 2) = (2 ^ (6 * K) : ℕ) := by
    rw [show (6 * (K : ℝ)) = ((6 * K : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_cast
  have hh := (abs_le.mp (oddLogarithmicCumulative_one_bound ht)).2
  have hp := finite_odd_reciprocal_le_odd_harmonic_prefix Q (2 ^ (6 * K)) hQ hodd
  have hf : oddLogarithmicCumulative (fun _ => 1) ((6 * (K : ℝ)) * Real.log 2) =
      ∑ n ∈ Finset.range (2 ^ (6 * K)),
        (if (n + 1) % 2 = 1 then (1 : ℝ) else 0) / (n + 1 : ℕ) := by
    unfold oddLogarithmicCumulative logarithmicCumulative
    rw [he, Nat.floor_natCast]
  rw [hf] at hh
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

theorem finite_ternary_reciprocal_budget (Q : Finset ℕ) (K : ℕ)
    (hQ : ∀ q ∈ Q, q ≤ 3 ^ K) :
    (∑ q ∈ Q, (1 : ℝ) / q) ≤ 1 + 2 * (K : ℝ) := by
  have hp := finite_reciprocal_le_harmonic_prefix Q (3 ^ K) hQ
  have hpow : 0 < (3 : ℕ) ^ K := by positivity
  have hh := finite_harmonic_bound (N := 3 ^ K) (by omega)
  have hl : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have he : Real.log ((3 ^ K : ℕ) : ℝ) = (K : ℝ) * Real.log 3 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [he] at hh
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

#print axioms finite_odd_dyadic_reciprocal_budget
#print axioms finite_ternary_reciprocal_budget

end CollatzCanonical.PeriodicCensusFloor
