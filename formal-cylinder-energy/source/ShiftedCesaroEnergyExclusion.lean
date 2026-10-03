import FiniteCylinderEnergyImplication
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCanonical.CesaroAbel

theorem sum_range_eq_prefix_add_reverse (f : ℕ → ℝ) (K C : ℕ) :
    (∑ i ∈ Finset.range (K + C + 1), f i) =
      (∑ i ∈ Finset.range C, f i) +
        ∑ j ∈ Finset.range (K + 1), f (K + C - j) := by
  rw [show K + C + 1 = C + (K + 1) by omega, Finset.sum_range_add]
  congr 1
  calc
    (∑ i ∈ Finset.range (K + 1), f (C + i)) =
        ∑ j ∈ Finset.range (K + 1), f (C + (K - j)) := by
      simpa using (Finset.sum_range_reflect (fun i => f (C + i)) (K + 1)).symm
    _ = ∑ j ∈ Finset.range (K + 1), f (K + C - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := by simpa using Finset.mem_range.mp hj
      congr 1
      omega

theorem diagonal_cesaro_square_bound (f : ℕ → ℝ) (a B : ℝ) (K C : ℕ)
    (hdiag : a ^ 2 * (∑ j ∈ Finset.range (K + 1), (f (K + C - j)) ^ 2) ≤ B) :
    a ^ 2 * (cesaroMean f (K + C)) ^ 2 ≤
      B / ((K + C : ℕ) + 1 : ℝ) +
        (a ^ 2 * ∑ i ∈ Finset.range C, (f i) ^ 2) /
          ((K + C : ℕ) + 1 : ℝ) := by
  have hj := mul_le_mul_of_nonneg_left
    (cesaroMean_square_le f (K + C)) (sq_nonneg a)
  have hd := div_le_div_of_nonneg_right hdiag
    (show (0 : ℝ) ≤ ((K + C : ℕ) + 1 : ℝ) by positivity)
  unfold cesaroMean at hj
  rw [sum_range_eq_prefix_add_reverse (fun i => (f i) ^ 2) K C] at hj
  change a ^ 2 * (cesaroMean f (K + C)) ^ 2 ≤ _
  calc
    _ ≤ a ^ 2 *
        ((∑ i ∈ Finset.range C, (f i) ^ 2) +
          ∑ j ∈ Finset.range (K + 1), (f (K + C - j)) ^ 2) /
            ((K + C : ℕ) + 1 : ℝ) := by
      simpa only [cesaroMean, mul_div_assoc] using hj
    _ = (a ^ 2 * ∑ j ∈ Finset.range (K + 1), (f (K + C - j)) ^ 2) /
          ((K + C : ℕ) + 1 : ℝ) +
        (a ^ 2 * ∑ i ∈ Finset.range C, (f i) ^ 2) /
          ((K + C : ℕ) + 1 : ℝ) := by ring
    _ ≤ _ := by linarith

theorem sublinear_energy_excludes_diagonal_cesaro
    (f E : ℕ → ℝ) (C : ℕ) (a L : ℝ)
    (ha : 0 < a) (hL : 0 < L)
    (hCes : Tendsto (cesaroMean f) atTop (𝓝 L))
    (hEsub : Tendsto (fun N => E N / ((N : ℝ) + 1)) atTop (𝓝 0))
    (hdiag : ∀ K : ℕ,
      a ^ 2 * (∑ j ∈ Finset.range (K + 1), (f (K + C - j)) ^ 2) ≤ E (K + C)) :
    False := by
  let D : ℝ := a ^ 2 * ∑ i ∈ Finset.range C, (f i) ^ 2
  have hshift : Tendsto (fun K : ℕ => K + C) atTop atTop :=
    tendsto_add_atTop_nat C
  have hleft : Tendsto (fun K => a ^ 2 * (cesaroMean f (K + C)) ^ 2)
      atTop (𝓝 (a ^ 2 * L ^ 2)) :=
    tendsto_const_nhds.mul ((hCes.comp hshift).pow 2)
  have hsmall : Tendsto (fun K : ℕ => D / ((K + C : ℕ) + 1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc] using
      (tendsto_const_div_atTop_nhds_zero_nat D).comp
        (tendsto_add_atTop_nat (C + 1))
  have hright : Tendsto (fun K => E (K + C) / ((K + C : ℕ) + 1 : ℝ) +
      D / ((K + C : ℕ) + 1 : ℝ)) atTop (𝓝 0) := by
    simpa using (hEsub.comp hshift).add hsmall
  have hle : a ^ 2 * L ^ 2 ≤ 0 := by
    apply le_of_tendsto_of_tendsto hleft hright
    exact Filter.Eventually.of_forall (fun K =>
      diagonal_cesaro_square_bound f a (E (K + C)) K C (hdiag K))
  exact (not_le_of_gt (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hL))) hle

#print axioms diagonal_cesaro_square_bound
#print axioms sublinear_energy_excludes_diagonal_cesaro

end CollatzCanonical.PeriodicCensusFloor
