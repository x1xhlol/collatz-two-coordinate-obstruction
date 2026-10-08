import ActualUniformBasinBoundary
import ForwardBasinFinite

set_option autoImplicit false
open Filter Topology

namespace CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao

/-- A single nonnegative boundary function tends to zero with a logarithmic
power rate and bounds every basin without a small ancestor. -/
theorem exists_uniform_basin_boundary_function :
    ∃ ε : ℝ → ℝ,
      (∀ M, 0 ≤ ε M) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
        ∀ᶠ M : ℝ in atTop, ε M = C * (Real.log M) ^ (-c)) ∧
      ∀ M : ℝ, ∀ v : ℕ, 0 < v → NoSmallAncestor v M → actualBasinDensity v ≤ ε M := by
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_uniform_noSmallAncestor_basin_bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hbound
  let R := max 2 T
  let ε : ℝ → ℝ := fun M => if R ≤ M then C * (Real.log M) ^ (-c) else 1
  have heq : ∀ᶠ M : ℝ in atTop, ε M = C * (Real.log M) ^ (-c) := by
    filter_upwards [eventually_ge_atTop R] with M hM
    exact if_pos hM
  have hnonneg : ∀ M, 0 ≤ ε M := by
    intro M
    by_cases hM : R ≤ M
    · have hM1 : 1 ≤ M := by dsimp only [R] at hM; linarith [le_max_left (2 : ℝ) T]
      change 0 ≤ if R ≤ M then _ else 1
      rw [if_pos hM]
      exact mul_nonneg hC (Real.rpow_nonneg (Real.log_nonneg hM1) _)
    · simp only [ε, if_neg hM, zero_le_one]
  have hlim : Tendsto (fun M : ℝ => C * (Real.log M) ^ (-c)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_rpow_neg_atTop hc).comp Real.tendsto_log_atTop).const_mul C
  refine ⟨ε, hnonneg, hlim.congr' (heq.mono (fun _ h => h.symm)), ⟨C, c, hC, hc, heq⟩, ?_⟩
  intro M v hv hno
  by_cases hM : R ≤ M
  · change actualBasinDensity v ≤ if R ≤ M then _ else 1
    rw [if_pos hM]
    exact hT M ((le_max_right (2 : ℝ) T).trans hM) v hv hno
  · change actualBasinDensity v ≤ if R ≤ M then _ else 1
    rw [if_neg hM]
    exact (actualBasinDensity_bounds v).2

/-- The density bound is uniform over all sufficiently large targets in
one fixed backward basin. -/
theorem fixed_basin_density_uniform_zero (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : ℕ, ∀ v : ℕ, V < v → (∃ K, iterate K v = N) → actualBasinDensity v < ε := by
  obtain ⟨E, _, hlim, _, hbound⟩ := exists_uniform_basin_boundary_function
  obtain ⟨M, hM, hsmall⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hlim.eventually_lt_const hε)).exists
  obtain ⟨V, hV⟩ := eventually_basin_targets_have_no_small_ancestor (Nat.floor M) N
  refine ⟨V, ?_⟩
  intro v hv htarget
  apply lt_of_le_of_lt (hbound M v (by omega) _) hsmall
  intro q _ hq hhit
  exact hV v hv htarget q (Nat.le_floor hq) hhit

theorem fixed_basin_density_tendsto_zero (N : ℕ) :
    Tendsto actualBasinDensity
      (atTop ⊓ 𝓟 {v : ℕ | ∃ K, iterate K v = N}) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨V, hV⟩ := fixed_basin_density_uniform_zero N hε
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_gt_atTop V] with v hv htarget
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (actualBasinDensity_bounds v).1]
  exact hV v hv htarget

#print axioms exists_uniform_basin_boundary_function
#print axioms fixed_basin_density_uniform_zero
#print axioms fixed_basin_density_tendsto_zero

end CollatzCylinderPacking.Arithmetic
