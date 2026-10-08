import PadicIntegerEnvelope
import CanonicalIntegerEnvelope
import CanonicalHaarLimitIdentification
import ActualUnconditionalCanonicalTrace
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

set_option autoImplicit false
set_option maxHeartbeats 500000

open MeasureTheory Filter
open scoped Topology ENNReal
open Erdos1135.Tao
open CollatzCanonical.CesaroAbel
open CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem le_limit_of_eventually_le_cesaro {f : ℕ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ k : ℕ in atTop, a ≤ f k)
    (hL : Tendsto (cesaroMean f) atTop (𝓝 L)) : a ≤ L := by
  have hclip : Tendsto (fun k => min a (f k)) atTop (𝓝 a) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hf] with k hk
    exact (min_eq_left hk).symm
  have hc : Tendsto (cesaroMean (fun k => min a (f k))) atTop (𝓝 a) := by
    change Tendsto (fun k : ℕ =>
      (∑ i ∈ Finset.range (k + 1), min a (f i)) / ((k : ℝ) + 1)) atTop (𝓝 a)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one,
      div_eq_mul_inv, mul_comm] using hclip.cesaro.comp (tendsto_add_atTop_nat 1)
  apply le_of_tendsto_of_tendsto hc hL
  exact Eventually.of_forall fun k => by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum fun j _ => min_le_right _ _

theorem lowerSemicontinuous_canonical_density_le_integer_trace
    (h : ℤ_[3] → ℝ≥0∞) (hh : LowerSemicontinuous h)
    (hmeasure : padicThreeHaar.withDensity h = canonicalSyracuseMeasure)
    (n : ℕ) (hn : 0 < n) :
    h (n : ℤ_[3]) ≤ ENNReal.ofReal
      (CollatzCylinderPacking.Arithmetic.actualDensityValue
        CollatzCylinderPacking.Arithmetic.actualFirstHitDensity n) := by
  apply le_of_forall_lt_imp_le_of_dense
  intro a ha
  have ha_top : a ≠ ⊤ := ne_of_lt (lt_of_lt_of_le ha le_top)
  obtain ⟨r, hr⟩ := CollatzCylinderPacking.Arithmetic.padic_cylinder_subset_nhds
    (hh (n : ℤ_[3]) a ha)
  have hbound : ∀ᶠ k : ℕ in atTop,
      a.toReal ≤ CollatzCylinderPacking.Arithmetic.canonicalRho k n := by
    filter_upwards [eventually_ge_atTop r] with k hk
    let C : Set ℤ_[3] := {x | PadicInt.toZModPow k x = (n : ZMod (3 ^ k))}
    have hC : MeasurableSet C := padic_cylinder_measurable k _
    have hpoint : ∀ x ∈ C, a ≤ h x := by
      intro x hx
      apply le_of_lt
      apply hr
      apply CollatzCylinderPacking.Arithmetic.padic_projection_refines hk
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
  have hlimit :=
    (CollatzCylinderPacking.Arithmetic.actual_unconditional_canonical_identification hn).2.2.1
  have hle := le_limit_of_eventually_le_cesaro hbound hlimit
  rw [← ENNReal.ofReal_toReal ha_top]
  apply ENNReal.ofReal_le_ofReal
  simpa only [CollatzCylinderPacking.Arithmetic.actualDensityValue, mul_comm, mul_left_comm,
    mul_assoc] using hle

#print axioms lowerSemicontinuous_canonical_density_le_integer_trace

theorem canonicalIntegerEnvelope_normalized_le_self
    {β : ℝ≥0∞} (hβ : β ≠ 0)
    (hmeasure : padicThreeHaar.withDensity
      (fun x => β⁻¹ * canonicalIntegerEnvelope x) = canonicalSyracuseMeasure) :
    ∀ x, β⁻¹ * canonicalIntegerEnvelope x ≤ canonicalIntegerEnvelope x := by
  have hlsc : LowerSemicontinuous (fun x => β⁻¹ * canonicalIntegerEnvelope x) :=
    (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr hβ)).comp_lowerSemicontinuous
      canonicalIntegerEnvelope_lowerSemicontinuous (fun _ _ h => mul_le_mul_right h _)
  apply padicIntegerEnvelope_maximal actualIntegerTrace _ hlsc
  intro n hn
  exact lowerSemicontinuous_canonical_density_le_integer_trace _ hlsc hmeasure n hn

theorem canonicalIntegerEnvelope_normalizing_mass_eq_one
    {β : ℝ≥0∞} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hpoint : 0 < canonicalIntegerEnvelope (1 : ℤ_[3]))
    (hmeasure : padicThreeHaar.withDensity
      (fun x => β⁻¹ * canonicalIntegerEnvelope x) = canonicalSyracuseMeasure) : β = 1 := by
  have hle := canonicalIntegerEnvelope_normalized_le_self (ne_of_gt hβpos) hmeasure
    (1 : ℤ_[3])
  have hfin : canonicalIntegerEnvelope (1 : ℤ_[3]) ≠ ⊤ :=
    ne_of_lt ((canonicalIntegerEnvelope_natCast_le 1 (by omega)).trans_lt
      (actualIntegerTrace_lt_top 1))
  have hinv : β⁻¹ ≤ 1 := by
    apply (ENNReal.mul_le_mul_iff_left (ne_of_gt hpoint) hfin).mp
    simpa only [one_mul] using hle
  exact le_antisymm hβle (ENNReal.inv_le_one.mp hinv)

#print axioms canonicalIntegerEnvelope_normalized_le_self
#print axioms canonicalIntegerEnvelope_normalizing_mass_eq_one

end CollatzCanonical.IntegerStationaryEnvelope
