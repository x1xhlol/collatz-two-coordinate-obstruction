import FirstHitPartialBounds
import ActualGreenSeries
import PeriodicLoopConvolution
import CanonicalCylinderAbel

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic

theorem canonical_cumulative_eq_arithmetic {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), canonicalRho k N) =
      ∑ k ∈ Finset.range (K + 1), (3 : ℝ) ^ k * arithmeticMass k N := by
  apply Finset.sum_congr rfl
  intro k _
  exact canonicalRho_eq_arithmetic hN k

/-- The actual canonical cylinder depth mean at a nonperiodic target,
conditional only on the explicitly stated first-hit mean limit. -/
theorem canonical_depth_mean_no_return_of_first_hit_mean {N : ℕ} (hN : 0 < N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 L) := by
  have he := tendsto_const_div_atTop_nhds_zero_nat (if N % 2 = 0 then (1 : ℝ) else 0)
  have h := he.add hF
  simp only [zero_add] at h
  convert h using 1
  funext K
  rw [canonical_cumulative_eq_arithmetic hN K, arithmetic_cumulative_no_return hN hno K]
  ring

/-- The actual periodic cylinder depth mean. The period's odd-source count
is positive and its loop weight contracts by the checked cycle identities. -/
theorem canonical_depth_mean_periodic_of_first_hit_mean {N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 (L / (1 - orbitRatio r N))) := by
  have hk := positive_cycle_oddCount_pos hN hperiod.positive hperiod.returns
  have hb := positive_cycle_ratio_bounds hN hperiod.positive hperiod.returns
  obtain ⟨C, hC, hbound⟩ := first_hit_partial_sum_linear hN
  have habs : ∀ K : ℕ, |firstHitPartialSum K N| ≤ C * ((K : ℝ) + 1) := by
    intro K
    rw [abs_of_nonneg (hbound K).1]
    exact (hbound K).2
  have hc := CollatzCanonical.PeriodicConvolution.loop_convolution_tendsto_of_linear_bound
    hk hb.1.le hb.2 hF hC habs
  have he := tendsto_const_div_atTop_nhds_zero_nat (if N % 2 = 0 then (1 : ℝ) else 0)
  have h := he.add hc
  simp only [zero_add] at h
  convert h using 1
  funext K
  rw [canonical_cumulative_eq_arithmetic hN K, arithmetic_cumulative_periodic hN hperiod K]
  simp only [CollatzCanonical.PeriodicConvolution.loopConvolution, Nat.mul_comm]
  ring

theorem canonical_cesaro_no_return_of_first_hit_mean {N : ℕ} (hN : 0 < N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 L) :=
  cesaroMean_of_depth_mean (canonical_depth_mean_no_return_of_first_hit_mean hN hno hF)

theorem canonical_cesaro_periodic_of_first_hit_mean {N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 (L / (1 - orbitRatio r N))) :=
  cesaroMean_of_depth_mean (canonical_depth_mean_periodic_of_first_hit_mean hN hperiod hF)

theorem canonical_abel_no_return_of_first_hit_mean {N : ℕ} (hN : 0 < N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 L) :=
  canonical_cylinder_abel_of_depth_mean hN
    (canonical_depth_mean_no_return_of_first_hit_mean hN hno hF)

theorem canonical_abel_periodic_of_first_hit_mean {N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 (L / (1 - orbitRatio r N))) :=
  canonical_cylinder_abel_of_depth_mean hN
    (canonical_depth_mean_periodic_of_first_hit_mean hN hperiod hF)

/-- Both target cases use the same actual cycle factor as the exact Green
series. The first-hit mean remains an explicit analytic input. -/
theorem canonical_depth_mean_of_first_hit_mean {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 (greenCycleFactor 1 N * L)) := by
  classical
  by_cases hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · have hp : LeastPositivePeriod N (Nat.find hret) := by
      refine ⟨(Nat.find_spec hret).1, (Nat.find_spec hret).2, ?_⟩
      intro d hd hhit
      exact Nat.find_min' hret ⟨hd, hhit⟩
    have h := canonical_depth_mean_periodic_of_first_hit_mean hN hp hF
    simpa only [greenCycleFactor, dif_pos hret, Real.rpow_one, div_eq_mul_inv, mul_comm] using h
  · have hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N := by
      intro d hd hh
      exact hret ⟨d, hd, hh⟩
    simpa only [greenCycleFactor, dif_neg hret, one_mul] using
      canonical_depth_mean_no_return_of_first_hit_mean hN hno hF

theorem canonical_cesaro_of_first_hit_mean {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 (greenCycleFactor 1 N * L)) :=
  cesaroMean_of_depth_mean (canonical_depth_mean_of_first_hit_mean hN hF)

theorem canonical_abel_of_first_hit_mean {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hF : Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 (greenCycleFactor 1 N * L)) :=
  canonical_cylinder_abel_of_depth_mean hN (canonical_depth_mean_of_first_hit_mean hN hF)

end CollatzCylinderPacking.Arithmetic
