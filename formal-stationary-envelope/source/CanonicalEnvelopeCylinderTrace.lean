import CanonicalEnvelopeStationary

set_option autoImplicit false
set_option maxHeartbeats 600000

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
open Erdos1135.Tao CollatzCylinderPacking.Arithmetic CollatzCanonical.CesaroAbel

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalIntegerEnvelope_greatest
    (h : ℤ_[3] → ℝ≥0∞) (hh : LowerSemicontinuous h)
    (hmeasure : padicThreeHaar.withDensity h = canonicalSyracuseMeasure) :
    h ≤ canonicalIntegerEnvelope := by
  apply padicIntegerEnvelope_maximal actualIntegerTrace h hh
  intro n hn
  exact lowerSemicontinuous_canonical_density_le_integer_trace h hh hmeasure n hn

theorem lsc_canonical_density_eventually_cylinder_lower
    (h : ℤ_[3] → ℝ≥0∞) (hh : LowerSemicontinuous h)
    (hmeasure : padicThreeHaar.withDensity h = canonicalSyracuseMeasure)
    (n : ℕ) (a : ℝ≥0∞) (ha : a < h (n : ℤ_[3])) :
    ∀ᶠ k : ℕ in atTop, a.toReal ≤ canonicalRho k n := by
  obtain ⟨r, hr⟩ := padic_cylinder_subset_nhds (hh (n : ℤ_[3]) a ha)
  filter_upwards [eventually_ge_atTop r] with k hk
  let C : Set ℤ_[3] := {x | PadicInt.toZModPow k x = (n : ZMod (3 ^ k))}
  have hC : MeasurableSet C := padic_cylinder_measurable k _
  have hpoint : ∀ x ∈ C, a ≤ h x := by
    intro x hx
    apply le_of_lt
    apply hr
    apply padic_projection_refines hk
    simpa only [map_natCast] using hx
  have hmass : a * (3 ^ k : ℝ≥0∞)⁻¹ ≤ canonicalSyracuseMeasure C := by
    rw [← hmeasure, withDensity_apply h hC]
    calc
      _ = ∫⁻ _ : ℤ_[3] in C, a ∂padicThreeHaar := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact congrArg (fun v => a * v) (padicThreeHaar_cylinder k _).symm
      _ ≤ ∫⁻ x : ℤ_[3] in C, h x ∂padicThreeHaar := by
        apply lintegral_mono_ae
        exact (ae_restrict_iff' hC).mpr (Eventually.of_forall hpoint)
  have hreal := ENNReal.toReal_mono (measure_ne_top canonicalSyracuseMeasure C) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at hreal
  change a.toReal ≤ (3 : ℝ) ^ k * (canonicalSyracuseMeasure C).toReal
  have hp : 0 < (3 : ℝ) ^ k := by positivity
  have hm := mul_le_mul_of_nonneg_left hreal hp.le
  have he : (3 : ℝ) ^ k * (a.toReal * ((3 : ℝ) ^ k)⁻¹) = a.toReal := by
    field_simp
  rwa [he] at hm

theorem lsc_canonical_density_eventually_value_lower
    (h : ℤ_[3] → ℝ≥0∞) (hh : LowerSemicontinuous h)
    (hmeasure : padicThreeHaar.withDensity h = canonicalSyracuseMeasure)
    (n : ℕ) (hfin : h (n : ℤ_[3]) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (h (n : ℤ_[3])).toReal - ε ≤ canonicalRho k n := by
  by_cases hp : 0 < (h (n : ℤ_[3])).toReal - ε
  · have he : ENNReal.ofReal ((h (n : ℤ_[3])).toReal - ε) < h (n : ℤ_[3]) := by
      conv_rhs => rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp.le).mpr (by linarith)
    have hbound := lsc_canonical_density_eventually_cylinder_lower h hh hmeasure n _ he
    simpa only [ENNReal.toReal_ofReal hp.le] using hbound
  · exact Eventually.of_forall fun k => (le_of_not_gt hp).trans (canonicalRho_nonneg k n)

theorem canonicalIntegerEnvelope_eventually_cylinder_lower (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalIntegerEnvelope (n : ℤ_[3])).toReal - ε ≤ canonicalRho k n := by
  apply lsc_canonical_density_eventually_value_lower canonicalIntegerEnvelope
    canonicalIntegerEnvelope_lowerSemicontinuous canonicalIntegerEnvelope_withDensity n _ hε
  exact ne_of_lt ((canonicalIntegerEnvelope_natCast_le n hn).trans_lt
    (actualIntegerTrace_lt_top n))

theorem cesaro_abs_sub_tendsto_zero_of_lower_bound {f : ℕ → ℝ} {L : ℝ}
    (hmean : Tendsto (cesaroMean f) atTop (𝓝 L))
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, L - ε ≤ f k) :
    Tendsto (cesaroMean (fun k => |f k - L|)) atTop (𝓝 0) := by
  have hmin : Tendsto (fun k => min (f k) L) atTop (𝓝 L) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hlower (ε / 2) (by linarith)] with k hk
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (min_le_right _ _))]
    have hm : L - ε / 2 ≤ min (f k) L := le_min hk (by linarith)
    linarith
  have hminmean : Tendsto (cesaroMean (fun k => min (f k) L)) atTop (𝓝 L) := by
    change Tendsto (fun k : ℕ =>
      (∑ i ∈ Finset.range (k + 1), min (f i) L) / ((k : ℝ) + 1)) atTop (𝓝 L)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one,
      div_eq_mul_inv, mul_comm] using hmin.cesaro.comp (tendsto_add_atTop_nat 1)
  have he (k : ℕ) : cesaroMean (fun i => |f i - L|) k =
      cesaroMean f k + L - 2 * cesaroMean (fun i => min (f i) L) k := by
    have hterm (i : ℕ) : |f i - L| = f i + L - 2 * min (f i) L := by
      by_cases hi : f i ≤ L
      · rw [min_eq_left hi, abs_of_nonpos (sub_nonpos.mpr hi)]
        ring
      · rw [min_eq_right (le_of_not_ge hi), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hi))]
        ring
    unfold cesaroMean
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  have hlim := (hmean.add_const L).sub (hminmean.const_mul 2)
  have hzero : L + L - 2 * L = 0 := by ring
  simpa only [← he, hzero] using hlim

theorem canonicalRho_cesaro_abs_trace_of_lsc_value
    (h : ℤ_[3] → ℝ≥0∞) (hh : LowerSemicontinuous h)
    (hmeasure : padicThreeHaar.withDensity h = canonicalSyracuseMeasure)
    (n : ℕ) (hn : 0 < n) (hpoint : h (n : ℤ_[3]) = actualIntegerTrace n) :
    Tendsto (cesaroMean (fun k =>
      |canonicalRho k n - actualDensityValue actualFirstHitDensity n|)) atTop (𝓝 0) := by
  apply cesaro_abs_sub_tendsto_zero_of_lower_bound
  · simpa only [actualDensityValue, mul_comm, mul_left_comm, mul_assoc] using
      (actual_unconditional_canonical_identification hn).2.2.1
  · intro ε hε
    have hfin : h (n : ℤ_[3]) ≠ ⊤ := by rw [hpoint]; exact ne_of_lt (actualIntegerTrace_lt_top n)
    have hb := lsc_canonical_density_eventually_value_lower h hh hmeasure n hfin hε
    have hnonneg : 0 ≤ actualDensityValue actualFirstHitDensity n := by
      by_cases hu : n % 3 = 0
      · rw [actual_trace_zero_of_multiple_three hu]
      · exact ((actual_trace_positive_iff_unit hn).mpr hu).le
    simpa only [hpoint, actualIntegerTrace, ENNReal.toReal_ofReal hnonneg] using hb

theorem canonicalRho_cesaro_abs_trace_of_envelope_eq (n : ℕ) (hn : 0 < n)
    (hpoint : canonicalIntegerEnvelope (n : ℤ_[3]) = actualIntegerTrace n) :
    Tendsto (cesaroMean (fun k =>
      |canonicalRho k n - actualDensityValue actualFirstHitDensity n|)) atTop (𝓝 0) :=
  canonicalRho_cesaro_abs_trace_of_lsc_value canonicalIntegerEnvelope
    canonicalIntegerEnvelope_lowerSemicontinuous canonicalIntegerEnvelope_withDensity n hn hpoint

theorem canonicalRho_mean_abs_trace_of_envelope_eq (n : ℕ) (hn : 0 < n)
    (hpoint : canonicalIntegerEnvelope (n : ℤ_[3]) = actualIntegerTrace n) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K,
      |canonicalRho k n - actualDensityValue actualFirstHitDensity n|) / (K : ℝ))
      atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [cesaroMean, Nat.cast_add, Nat.cast_one] using
    canonicalRho_cesaro_abs_trace_of_envelope_eq n hn hpoint

#print axioms canonicalIntegerEnvelope_greatest
#print axioms canonicalIntegerEnvelope_eventually_cylinder_lower
#print axioms canonicalRho_cesaro_abs_trace_of_envelope_eq
#print axioms canonicalRho_mean_abs_trace_of_envelope_eq

end CollatzCanonical.IntegerStationaryEnvelope
