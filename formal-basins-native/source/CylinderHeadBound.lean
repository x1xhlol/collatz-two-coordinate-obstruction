import AdmissibleCylinderWords
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace CollatzCylinderPacking

def endpointMass (A k N : ℕ) : ℚ := (endpointCount A k N : ℚ) / 2 ^ A

theorem endpointMass_le (k i N : ℕ) :
    endpointMass (k + i) k N ≤ 1 / (2 : ℚ) ^ (k + 1) + 1 / (2 : ℚ) ^ (k + i) := by
  have hn := endpointCount_scaled_bound (k + i) k N
  simp only [Nat.add_sub_cancel_left] at hn
  have hc : 2 * (endpointCount (k + i) k N : ℚ) ≤ (2 : ℚ) ^ i + 2 := by
    exact_mod_cast hn
  unfold endpointMass
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (k + i))).mpr
  have he : (1 / (2 : ℚ) ^ (k + 1) + 1 / (2 : ℚ) ^ (k + i)) *
      (2 : ℚ) ^ (k + i) = (2 : ℚ) ^ i / 2 + 1 := by
    simp only [pow_add, pow_one]
    field_simp
  rw [he]
  linarith

theorem finite_dyadic_sum (k L : ℕ) :
    (∑ i ∈ Finset.range L, 1 / (2 : ℚ) ^ (k + i)) =
      2 / (2 : ℚ) ^ k - 2 / (2 : ℚ) ^ (k + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_add, pow_succ]
    field_simp
    ring

theorem finite_dyadic_sum_le (k L : ℕ) :
    (∑ i ∈ Finset.range L, 1 / (2 : ℚ) ^ (k + i)) ≤ 2 / (2 : ℚ) ^ k := by
  rw [finite_dyadic_sum]
  have hp : (0 : ℚ) ≤ 2 / (2 : ℚ) ^ (k + L) :=
    div_nonneg (by norm_num) (le_of_lt (pow_pos (by norm_num) _))
  exact sub_le_self _ hp

theorem endpoint_head_general (k L N : ℕ) :
    (∑ i ∈ Finset.range L, endpointMass (k + i) k N) ≤
      (L : ℚ) / (2 : ℚ) ^ (k + 1) + 2 / (2 : ℚ) ^ k := by
  calc
    (∑ i ∈ Finset.range L, endpointMass (k + i) k N) ≤
        ∑ i ∈ Finset.range L,
          (1 / (2 : ℚ) ^ (k + 1) + 1 / (2 : ℚ) ^ (k + i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact endpointMass_le k i N
    _ = (L : ℚ) / (2 : ℚ) ^ (k + 1) +
        ∑ i ∈ Finset.range L, 1 / (2 : ℚ) ^ (k + i) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
    _ ≤ (L : ℚ) / (2 : ℚ) ^ (k + 1) + 2 / (2 : ℚ) ^ k :=
      add_le_add (le_refl ((L : ℚ) / (2 : ℚ) ^ (k + 1))) (finite_dyadic_sum_le k L)

/-- The finite A=k,...,5k-1 contribution in the optimal-cylinder estimate.
This theorem has no stationary-measure or infinite-series hypothesis. -/
theorem endpoint_head_bound (k N : ℕ) :
    (∑ i ∈ Finset.range (4 * k), endpointMass (k + i) k N) ≤
      (2 * (k : ℚ) + 2) / (2 : ℚ) ^ k := by
  calc
    (∑ i ∈ Finset.range (4 * k), endpointMass (k + i) k N) ≤
        ((4 * k : ℕ) : ℚ) / (2 : ℚ) ^ (k + 1) + 2 / (2 : ℚ) ^ k :=
      endpoint_head_general k (4 * k) N
    _ = (2 * (k : ℚ) + 2) / (2 : ℚ) ^ k := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      field_simp
      ring

#print axioms endpointMass_le
#print axioms endpoint_head_bound

end CollatzCylinderPacking
