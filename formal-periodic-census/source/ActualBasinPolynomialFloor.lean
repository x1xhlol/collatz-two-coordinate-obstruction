import FrozenSeedPeriodicPrefix
import ActualBasinPeriodicMean

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking.Arithmetic
open CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem frozen_seed_periodic_density_bound
    {N r : ℕ}
    (hprefix : ∀ m : ℕ, 1 ≤ m → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      (2 / 3 : ℝ) ≤ ((r : ℝ) / (X : ℝ)) *
        (∑ q ∈ Finset.range (32 * X), basinIndicator N q *
          (if Odd q then terminalFanEnvelope m (q : ZMod (3 ^ m)) else 0)) +
        44 * (r : ℝ) * (explicitSyracuseMixingCoefficient : ℝ) / (m : ℝ) ^ 2) :
    (2 / 3 : ℝ) ≤ (128 * (r : ℝ) / 9) * actualBasinDensity N := by
  have hfixed (m : ℕ) (hm : 1 ≤ m) :
      (2 / 3 : ℝ) ≤ (128 * (r : ℝ) / 9) * actualBasinDensity N +
        44 * (r : ℝ) * (explicitSyracuseMixingCoefficient : ℝ) / (m : ℝ) ^ 2 := by
    obtain ⟨X0, hX0⟩ := hprefix m hm
    apply ge_of_tendsto
      ((actual_basin_oddTerminalFan_scaled_limit N m (r : ℝ)).add_const
        (44 * (r : ℝ) * (explicitSyracuseMixingCoefficient : ℝ) / (m : ℝ) ^ 2))
    exact eventually_atTop.2 ⟨X0, fun X hX => by
      simpa only [oddTerminalFan] using hX0 X hX⟩
  have herr : Tendsto (fun m : ℕ =>
      44 * (r : ℝ) * (explicitSyracuseMixingCoefficient : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat
      (44 * (r : ℝ) * (explicitSyracuseMixingCoefficient : ℝ))).mul
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    simpa only [mul_zero, one_div, div_eq_mul_inv, pow_two, mul_inv_rev, mul_assoc, one_mul]
      using h
  have h := ge_of_tendsto
    (herr.const_add ((128 * (r : ℝ) / 9) * actualBasinDensity N))
    (eventually_atTop.2 ⟨1, hfixed⟩)
  simpa only [add_zero] using h

theorem actual_basin_polynomial_lower_density
    {N : ℕ} (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    3 / (128 * (predecessorSeedMultiplier : ℝ) * (N : ℝ)) ≤ actualBasinDensity N := by
  obtain ⟨r, hr, hbound, hprefix⟩ :=
    exists_frozen_seed_eventual_periodic_prefix hN hunit
  have hmain := frozen_seed_periodic_density_bound hprefix
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hfloor : 3 / (64 * (r : ℝ)) ≤ actualBasinDensity N := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (r : ℝ))).2
    nlinarith only [hmain]
  have hden : 64 * (r : ℝ) ≤
      128 * (predecessorSeedMultiplier : ℝ) * (N : ℝ) := by
    have hbound' : (r : ℝ) ≤ (predecessorSeedMultiplier : ℝ) * (2 * (N : ℝ)) := by
      exact_mod_cast hbound
    nlinarith only [hbound']
  exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
    (by positivity : (0 : ℝ) < 64 * (r : ℝ)) hden).trans hfloor

#print axioms frozen_seed_periodic_density_bound
#print axioms actual_basin_polynomial_lower_density

end
end CollatzCanonical.PeriodicCensusFloor
