import CycleTraceRatioFloor
import ActualUnconditionalCanonicalTrace
import ComponentPositivityEquivalences
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.CesaroAbel CollatzCanonical.ForwardComponent

noncomputable section

theorem cesaroMean_tendsto_of_tendsto {f : ℕ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (cesaroMean f) atTop (𝓝 L) := by
  have h := hf.cesaro.comp (tendsto_add_atTop_nat 1)
  simpa only [cesaroMean, Function.comp_def, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv, mul_comm] using h

theorem cesaroMean_square_le (f : ℕ → ℝ) (K : ℕ) :
    (cesaroMean f K) ^ 2 ≤ cesaroMean (fun k => (f k) ^ 2) K := by
  simpa only [cesaroMean, Finset.card_range, Nat.cast_add, Nat.cast_one] using
    (sum_div_card_sq_le_sum_sq_div_card (s := Finset.range (K + 1)) (f := f))

theorem finite_sum_square_le_of_cesaro {ι : Type*} (s : Finset ι)
    (f : ℕ → ι → ℝ) (g : ι → ℝ) (B : ℝ)
    (hlim : ∀ i ∈ s, Tendsto (cesaroMean (fun k => f k i)) atTop (𝓝 (g i)))
    (hbound : ∀ᶠ k in atTop, ∑ i ∈ s, (f k i) ^ 2 ≤ B) :
    ∑ i ∈ s, (g i) ^ 2 ≤ B := by
  let upper : ℕ → ℝ := fun k => max (∑ i ∈ s, (f k i) ^ 2) B
  have hu : Tendsto upper atTop (𝓝 B) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hbound] with k hk
    exact (max_eq_right hk).symm
  have hleft : Tendsto (fun K => ∑ i ∈ s, (cesaroMean (fun k => f k i) K) ^ 2)
      atTop (𝓝 (∑ i ∈ s, (g i) ^ 2)) :=
    tendsto_finset_sum s (fun i hi => (hlim i hi).pow 2)
  apply le_of_tendsto_of_tendsto hleft (cesaroMean_tendsto_of_tendsto hu)
  apply Filter.Eventually.of_forall
  intro K
  calc
    _ ≤ ∑ i ∈ s, cesaroMean (fun k => (f k i) ^ 2) K :=
      Finset.sum_le_sum (fun i _ => cesaroMean_square_le (fun k => f k i) K)
    _ = cesaroMean (fun k => ∑ i ∈ s, (f k i) ^ 2) K := by
      simp only [cesaroMean, ← Finset.sum_div]
      rw [Finset.sum_comm]
    _ ≤ cesaroMean upper K := by
      unfold cesaroMean
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum (fun k _ => le_max_left _ _)

/-- The energy uses exactly the positive representatives `1, ..., 3^k`. -/
def positiveCylinderSquareEnergy (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (3 ^ k), (canonicalRho k (n + 1) / ((n + 1 : ℕ) : ℝ)) ^ 2

theorem actual_normalized_cylinder_cesaro (n : ℕ) :
    Tendsto (cesaroMean (fun k => canonicalRho k (n + 1) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (actualDensityValue actualFirstHitDensity (n + 1) / ((n + 1 : ℕ) : ℝ))) := by
  have h := (actual_unconditional_canonical_identification
    (show 0 < n + 1 by omega)).2.2.1
  have hd := h.div_const ((n + 1 : ℕ) : ℝ)
  convert hd using 1
  · funext K
    simp only [cesaroMean, ← Finset.sum_div]
    ring
  · congr 1
    unfold actualDensityValue
    ring

theorem actual_normalized_trace_square_sum_le (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) (M : ℕ) :
    ∑ n ∈ Finset.range M,
      (actualDensityValue actualFirstHitDensity (n + 1) / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ B := by
  apply finite_sum_square_le_of_cesaro (Finset.range M)
    (fun k n => canonicalRho k (n + 1) / ((n + 1 : ℕ) : ℝ))
    (fun n => actualDensityValue actualFirstHitDensity (n + 1) / ((n + 1 : ℕ) : ℝ)) B
    (fun n _ => actual_normalized_cylinder_cesaro n)
  filter_upwards [eventually_ge_atTop M] with k hk
  have hpow : k ≤ 3 ^ k := by
    clear hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 3 ^ k := by positivity
      omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hk.trans hpow))
    (fun n _ _ => sq_nonneg _)).trans (henergy k)

theorem actual_normalized_trace_square_summable (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) :
    Summable (fun n : ℕ =>
      (actualDensityValue actualFirstHitDensity (n + 1) / ((n + 1 : ℕ) : ℝ)) ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _)
    (actual_normalized_trace_square_sum_le B henergy)

theorem actual_normalized_trace_tendsto_zero_of_finite_energy (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) :
    Tendsto (fun n : ℕ => actualDensityValue actualFirstHitDensity n / (n : ℝ))
      atTop (𝓝 0) := by
  have hsq := (actual_normalized_trace_square_summable B henergy).tendsto_atTop_zero
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((tendsto_order.mp hsq).2 (ε ^ 2) (sq_pos_of_pos hε))
  refine ⟨K, ?_⟩
  intro n hn
  have hs := hK n hn
  rw [dist_zero_right, Real.norm_eq_abs]
  nlinarith [sq_abs (actualDensityValue actualFirstHitDensity (n + 1) /
    ((n + 1 : ℕ) : ℝ)), abs_nonneg (actualDensityValue actualFirstHitDensity (n + 1) /
    ((n + 1 : ℕ) : ℝ))]

theorem universal_eventual_periodicity_of_finite_energy (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) :
    UniversalEventualPeriodicity := by
  apply nonperiodicGreenSublinear_iff_universalEventualPeriodicity.mp
  intro ε hε
  obtain ⟨V, hV⟩ := Metric.tendsto_atTop.mp
    (actual_normalized_trace_tendsto_zero_of_finite_energy B henergy) ε hε
  refine ⟨V, ?_⟩
  intro v hv _
  simpa only [dist_zero_right, Real.norm_eq_abs] using hV v (Nat.le_of_lt hv)

theorem positive_periodic_points_bounded_of_finite_energy (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) :
    ∃ V : ℕ, ∀ n : ℕ, 0 < n →
      (∃ k : ℕ, 0 < k ∧ iterate k n = n) → n ≤ V := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_cyclic_trace_ratio_floor
  obtain ⟨V, hV⟩ := Metric.tendsto_atTop.mp
    (actual_normalized_trace_tendsto_zero_of_finite_energy B henergy) c hc
  refine ⟨V, ?_⟩
  intro n hn hperiod
  by_contra hlarge
  have hv := hV n (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))
  simp only [dist_zero_right, Real.norm_eq_abs] at hv
  have hr : c ≤ actualDensityValue actualFirstHitDensity n / (n : ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (hfloor n hn hperiod)
  exact (not_lt_of_ge (hr.trans (le_abs_self _))) hv

theorem positive_periodic_points_finite_of_finite_energy (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) :
    {n : ℕ | 0 < n ∧ ∃ k : ℕ, 0 < k ∧ iterate k n = n}.Finite := by
  obtain ⟨V, hV⟩ := positive_periodic_points_bounded_of_finite_energy B henergy
  apply (Finset.finite_toSet (Finset.range (V + 1))).subset
  intro n hn
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hV n hn.1 hn.2))

/-- The finite-energy bound is the explicit unproved input. The conclusion
does not identify the finite collection of positive cycles. -/
theorem finite_cylinder_square_energy_consequences (B : ℝ)
    (henergy : ∀ k : ℕ, positiveCylinderSquareEnergy k ≤ B) :
    Tendsto (fun n : ℕ => actualDensityValue actualFirstHitDensity n / (n : ℝ))
      atTop (𝓝 0) ∧
    UniversalEventualPeriodicity ∧
    {n : ℕ | 0 < n ∧ ∃ k : ℕ, 0 < k ∧ iterate k n = n}.Finite :=
  ⟨actual_normalized_trace_tendsto_zero_of_finite_energy B henergy,
    universal_eventual_periodicity_of_finite_energy B henergy,
    positive_periodic_points_finite_of_finite_energy B henergy⟩

#print axioms finite_sum_square_le_of_cesaro
#print axioms actual_normalized_trace_square_summable
#print axioms finite_cylinder_square_energy_consequences

end
end CollatzCanonical.PeriodicCensusFloor
