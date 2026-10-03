import PowerPredecessorDensity
import BoundedPredecessorDensity
import NativePredecessorMixingBridge
import BasinPositiveNaturalCriterion
import CollatzPredecessorDensity

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor Erdos1135Predecessor.ND.PositiveDensity
open CollatzCylinderPacking.Arithmetic CollatzBasinMapBridges

theorem actual_basin_density_ge_power_floor {p : ℕ} {Cp : ℝ}
    (hp : 0 < p) (hCp : 0 ≤ Cp) (hmixp : Tao.syracFineScaleMixingAt p Cp)
    {N : ℕ} (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    powerDensityFloor p Cp (predecessorSeedMultiplier * (2 * N)) ≤ actualBasinDensity N := by
  have hdouble : ¬ 3 ∣ 2 * N := by omega
  obtain ⟨X0, hcount⟩ := generalTarget_predecessors_power_floor
    (a := 2 * N) (b := predecessorSeedBase) (C := explicitSyracuseMixingCoefficient)
    (N := predecessorSeedGeneration) (by omega) hdouble le_rfl
    explicitSyracuseMixing_six le_rfl hp hCp hmixp
  have hS : ∀ q ∈ CollatzPredecessorDensity.predecessors (2 * N),
      0 < q ∧ basinIndicator N q = 1 := by
    intro q hq
    exact ⟨hq.1, native_predecessor_double_basin hq.2⟩
  exact basin_density_ge_positive_count_rate _ N
    (powerDensityFloor p Cp (predecessorSeedMultiplier * (2 * N))) X0 hS hcount

theorem actual_basin_density_ge_power_exp {p : ℕ} {Cp : ℝ}
    (hp : 0 < p) (hCp : 0 ≤ Cp) (hmixp : Tao.syracFineScaleMixingAt p Cp)
    {N : ℕ} (hN : 0 < N) (hunit : N % 3 ≠ 0) :
    Real.exp (-Real.log 3 *
      (88 * Cp * ((predecessorSeedMultiplier * (2 * N) : ℕ) : ℝ)) ^ (1 / (p : ℝ))) /
      (256 * ((predecessorSeedMultiplier * (2 * N) : ℕ) : ℝ)) ≤ actualBasinDensity N :=
  (powerDensityFloor_ge_exp p Cp hCp
    (Nat.mul_pos predecessorSeedMultiplier_pos (by omega))).trans
      (actual_basin_density_ge_power_floor hp hCp hmixp hN hunit)

theorem actual_basin_density_each_power_lower :
    ∃ B : ℝ, 0 < B ∧ ∀ p : ℕ, 0 < p → ∃ A : ℝ, 0 < A ∧
      ∀ N : ℕ, 0 < N → N % 3 ≠ 0 →
        Real.exp (-A * (N : ℝ) ^ (1 / (p : ℝ))) / (B * (N : ℝ)) ≤
          actualBasinDensity N := by
  let U : ℝ := 2 * (predecessorSeedMultiplier : ℝ)
  have hK : (0 : ℝ) < predecessorSeedMultiplier := by
    exact_mod_cast predecessorSeedMultiplier_pos
  have hU : 0 < U := mul_pos (by norm_num) hK
  refine ⟨256 * U, mul_pos (by norm_num) hU, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hmixp⟩ := predecessor_mixing_each_positive_power p hp
  let A0 : ℝ := Real.log 3 * (88 * Cp * U) ^ (1 / (p : ℝ))
  have hbase : 0 ≤ 88 * Cp * U :=
    mul_nonneg (mul_nonneg (by norm_num) hCp) hU.le
  have hA0 : 0 ≤ A0 := mul_nonneg (Real.log_nonneg (by norm_num))
    (Real.rpow_nonneg hbase _)
  refine ⟨A0 + 1, by linarith, ?_⟩
  intro N hN hunit
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hheight : ((predecessorSeedMultiplier * (2 * N) : ℕ) : ℝ) = U * (N : ℝ) := by
    dsimp [U]
    push_cast
    ring
  have hpwr : 0 ≤ (N : ℝ) ^ (1 / (p : ℝ)) := Real.rpow_nonneg hn.le _
  have hnum : Real.exp (-(A0 + 1) * (N : ℝ) ^ (1 / (p : ℝ))) ≤
      Real.exp (-A0 * (N : ℝ) ^ (1 / (p : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he := actual_basin_density_ge_power_exp hp hCp hmixp hN hunit
  rw [hheight, show 88 * Cp * (U * (N : ℝ)) = (88 * Cp * U) * (N : ℝ) by ring,
    Real.mul_rpow hbase hn.le] at he
  have he' : Real.exp (-A0 * (N : ℝ) ^ (1 / (p : ℝ))) /
      ((256 * U) * (N : ℝ)) ≤ actualBasinDensity N := by
    simpa only [A0, neg_mul, mul_assoc] using he
  exact (div_le_div_of_nonneg_right hnum
    (mul_nonneg (mul_nonneg (by norm_num) hU.le) hn.le)).trans he'

#print axioms actual_basin_density_ge_power_floor
#print axioms actual_basin_density_ge_power_exp
#print axioms actual_basin_density_each_power_lower

end CollatzCanonical.BoundedInverseSeed
