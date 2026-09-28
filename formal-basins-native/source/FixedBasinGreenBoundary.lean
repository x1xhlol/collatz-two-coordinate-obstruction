import UniformBasinBoundaryFunction
import BasinWeightedDensityComparison

set_option autoImplicit false
open Filter Topology

namespace CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian CollatzCanonical.GreenKernelScalars

theorem actualFirstHitDensity_nonneg (v : ℕ) : 0 ≤ actualFirstHitDensity v := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (actual_firstHitWeight_full_mean v)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact div_nonneg (logarithmicCumulative_nonneg
    (fun q => (firstHitWeight_bounds v q).1) t) ht.le

theorem green_density_ratio_of_nonperiodic {v : ℕ} (hv : 0 < v)
    (hno : ¬ ∃ r : ℕ, 0 < r ∧ iterate r v = v) :
    actualDensityValue actualFirstHitDensity v / (v : ℝ) =
      delta * actualFirstHitDensity v := by
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [actualDensityValue, greenCycleFactor, dif_neg hno, mul_one]
  field_simp

/-- The critical Green value divided by the target tends to zero uniformly
as the target grows inside a fixed backward basin. -/
theorem fixed_basin_green_ratio_uniform_zero (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : ℕ, ∀ v : ℕ, V < v → (∃ K, iterate K v = N) →
      |actualDensityValue actualFirstHitDensity v / (v : ℝ)| < ε := by
  obtain ⟨V₁, hV₁⟩ := fixed_basin_density_uniform_zero N
    (div_pos hε delta_pos)
  obtain ⟨V₂, hV₂⟩ := eventually_basin_targets_nonperiodic N
  obtain ⟨_, _, hcompare⟩ := actual_basin_and_weighted_density_comparison
  refine ⟨max V₁ V₂, ?_⟩
  intro v hv htarget
  have hvpos : 0 < v := by omega
  have hratio := green_density_ratio_of_nonperiodic hvpos
    (hV₂ v (by omega) htarget)
  have hb := hV₁ v (by omega) htarget
  have hsmall : delta * actualBasinDensity v < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ delta_pos).mp hb
  rw [hratio, abs_of_nonneg (mul_nonneg delta_pos.le (actualFirstHitDensity_nonneg v))]
  exact (mul_le_mul_of_nonneg_left (hcompare v).1 delta_pos.le).trans_lt hsmall

theorem fixed_basin_green_ratio_tendsto_zero (N : ℕ) :
    Tendsto (fun v : ℕ => actualDensityValue actualFirstHitDensity v / (v : ℝ))
      (atTop ⊓ 𝓟 {v : ℕ | ∃ K, iterate K v = N}) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨V, hV⟩ := fixed_basin_green_ratio_uniform_zero N hε
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_gt_atTop V] with v hv htarget
  rw [Real.dist_eq, sub_zero]
  exact hV v hv htarget

theorem fixed_basin_boundary_limits (N : ℕ) :
    Tendsto actualBasinDensity
      (atTop ⊓ 𝓟 {v : ℕ | ∃ K, iterate K v = N}) (𝓝 0) ∧
    Tendsto (fun v : ℕ => actualDensityValue actualFirstHitDensity v / (v : ℝ))
      (atTop ⊓ 𝓟 {v : ℕ | ∃ K, iterate K v = N}) (𝓝 0) :=
  ⟨fixed_basin_density_tendsto_zero N, fixed_basin_green_ratio_tendsto_zero N⟩

#print axioms actualFirstHitDensity_nonneg
#print axioms fixed_basin_green_ratio_uniform_zero
#print axioms fixed_basin_green_ratio_tendsto_zero
#print axioms fixed_basin_boundary_limits

end CollatzCylinderPacking.Arithmetic
