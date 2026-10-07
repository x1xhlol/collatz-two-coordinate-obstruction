import LastVisitGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem inverseEndpoint_forward_growth {n a : ℕ}
    (h : (2 ^ a * n) % 3 = 2) :
    (n : ℝ) + 1 ≤ (3 / 2 : ℝ) * ((inverseEndpoint n a : ℝ) + 1) := by
  have hs := oddPredecessor_spec h
  have he := step_odd hs.2.1
  rw [hs.2.2] at he
  have hp : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by decide)
  have hm : n ≤ 2 ^ a * n := by simpa only [one_mul] using Nat.mul_le_mul_right n hp
  have hn : 2 * n ≤ 3 * inverseEndpoint n a + 1 := by
    change 2 * n ≤ 3 * oddPredecessor (2 ^ a * n) + 1
    omega
  have hr : (2 : ℝ) * n ≤ 3 * (inverseEndpoint n a : ℝ) + 1 := by exact_mod_cast hn
  nlinarith

theorem inverseEndpoint_log_forward_growth {n a : ℕ}
    (h : (2 ^ a * n) % 3 = 2) :
    Real.log ((n : ℝ) + 1) ≤
      Real.log ((inverseEndpoint n a : ℝ) + 1) + Real.log (3 / 2 : ℝ) := by
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < n + 1)
    (inverseEndpoint_forward_growth h)
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  linarith

theorem IsActualInversePath.log_growth_over_gap {n : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (k d : ℕ) :
    Real.log ((x k : ℝ) + 1) ≤ Real.log ((x (k + d) : ℝ) + 1) +
      Real.log (3 / 2 : ℝ) * (d : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨a, ha, hnext⟩ := hx.2 (k + d)
    have hs := inverseEndpoint_log_forward_growth ha
    rw [← hnext] at hs
    have he : k + (d + 1) = k + d + 1 := by omega
    rw [he, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem IsActualInversePath.log_backward_growth {n : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) {k t : ℕ} (hkt : k ≤ t) :
    Real.log ((x k : ℝ) + 1) ≤ Real.log ((x t : ℝ) + 1) +
      Real.log (3 / 2 : ℝ) * ((t - k : ℕ) : ℝ) := by
  simpa only [Nat.add_sub_of_le hkt] using hx.log_growth_over_gap k (t - k)

theorem log_three_halves_nonneg : 0 ≤ Real.log (3 / 2 : ℝ) :=
  Real.log_nonneg (by norm_num)

#print axioms inverseEndpoint_forward_growth
#print axioms inverseEndpoint_log_forward_growth
#print axioms IsActualInversePath.log_growth_over_gap
#print axioms IsActualInversePath.log_backward_growth
#print axioms log_three_halves_nonneg

end CollatzCylinderPacking.Arithmetic.InverseDoob
