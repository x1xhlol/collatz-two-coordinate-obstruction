import CanonicalHaarDensity
import PadicCylinderDetermining
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Identifying the actual Haar L1 limit

Continuity of integrals and the L1 norm gives mass one and nonnegativity
of the limit. Its cylinder integrals identify the canonical probability
with the measure having the nonnegative representative |L| as density.
-/

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

/-- The signed representative of an actual Haar L1 limit has integral one. -/
theorem canonicalHaarL1_limit_integral
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L)) :
    (∫ x : ℤ_[3], L x ∂padicThreeHaar) = 1 := by
  have hi (n : ℕ) : (∫ x : ℤ_[3], canonicalHaarL1 n x ∂padicThreeHaar) = 1 := by
    rw [integral_congr_ae (canonicalHaarL1_coe n), canonicalPadicRho_integral]
  have h := (MeasureTheory.continuous_integral.tendsto L).comp hL
  change Tendsto (fun n => ∫ x : ℤ_[3], canonicalHaarL1 n x ∂padicThreeHaar)
    atTop (𝓝 (∫ x : ℤ_[3], L x ∂padicThreeHaar)) at h
  simp only [hi] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The absolute value of the limit has mass one. -/
theorem canonicalHaarL1_limit_abs_integral
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L)) :
    (∫ x : ℤ_[3], |L x| ∂padicThreeHaar) = 1 := by
  have hn (n : ℕ) : ‖canonicalHaarL1 n‖ = 1 := by
    rw [L1.norm_eq_integral_norm]
    calc
      _ = ∫ x : ℤ_[3], canonicalPadicRho n x ∂padicThreeHaar := by
        apply integral_congr_ae
        filter_upwards [canonicalHaarL1_coe n] with x hx
        rw [hx, Real.norm_eq_abs, abs_of_nonneg (canonicalPadicRho_nonneg n x)]
      _ = 1 := canonicalPadicRho_integral n
  have h := hL.norm
  simp only [hn] at h
  have hnorm : ‖L‖ = 1 := tendsto_nhds_unique h tendsto_const_nhds
  simpa only [L1.norm_eq_integral_norm, Real.norm_eq_abs] using hnorm

/-- Nonnegativity is derived from mass and norm preservation, not assumed. -/
theorem canonicalHaarL1_limit_abs_ae
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L)) :
    (fun x => |L x|) =ᵐ[padicThreeHaar] L := by
  have hInt := L1.integrable_coeFn L
  have hzero : (∫ x : ℤ_[3], (|L x| - L x) ∂padicThreeHaar) = 0 := by
    rw [integral_sub hInt.abs hInt, canonicalHaarL1_limit_abs_integral L hL,
      canonicalHaarL1_limit_integral L hL]
    norm_num
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x => sub_nonneg.mpr (le_abs_self (L x))))
    (hInt.abs.sub hInt)).mp hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx

theorem canonicalHaarL1_limit_abs_integrable
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ) :
    Integrable (fun x => |L x|) padicThreeHaar :=
  (L1.integrable_coeFn L).abs

/-- The absolute representative preserves each eventually fixed cylinder integral. -/
theorem canonicalHaarL1_limit_abs_cylinder_integral
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L))
    (k : ℕ) (v : ZMod (3 ^ k)) :
    (∫ x : ℤ_[3] in {x | PadicInt.toZModPow k x = v}, |L x| ∂padicThreeHaar) =
      (canonicalSyracuseMeasure {x | PadicInt.toZModPow k x = v}).toReal := by
  let s : Set ℤ_[3] := {x | PadicInt.toZModPow k x = v}
  have ht := ((MeasureTheory.continuous_setIntegral s).tendsto L).comp hL
  have heq : (fun n => ∫ x in s, canonicalHaarL1 n x ∂padicThreeHaar) =ᶠ[atTop]
      fun _ => (canonicalSyracuseMeasure s).toReal := by
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [integral_congr_ae (ae_restrict_of_ae (canonicalHaarL1_coe n))]
    exact canonicalPadicRho_cylinder_integral hn v
  have hc : Tendsto (fun n => ∫ x in s, canonicalHaarL1 n x ∂padicThreeHaar)
      atTop (𝓝 (canonicalSyracuseMeasure s).toReal) :=
    tendsto_const_nhds.congr' heq.symm
  rw [integral_congr_ae (ae_restrict_of_ae (canonicalHaarL1_limit_abs_ae L hL))]
  exact tendsto_nhds_unique ht hc

/-- Cylinder uniqueness identifies the actual canonical measure with the density. -/
theorem canonicalSyracuseMeasure_eq_withDensity_abs_limit
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L)) :
    canonicalSyracuseMeasure = padicThreeHaar.withDensity (fun x => ENNReal.ofReal |L x|) := by
  have hInt := canonicalHaarL1_limit_abs_integrable L
  have hnn : 0 ≤ᵐ[padicThreeHaar] (fun x => |L x|) :=
    Eventually.of_forall (fun x => abs_nonneg (L x))
  letI : IsProbabilityMeasure
      (padicThreeHaar.withDensity (fun x => ENNReal.ofReal |L x|)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hInt hnn,
      canonicalHaarL1_limit_abs_integral L hL]
    norm_num
  apply padic_probability_eq_of_cylinders
  intro k v
  rw [withDensity_apply _ (padic_cylinder_measurable k v),
    ← ofReal_integral_eq_lintegral_ofReal hInt.restrict (ae_restrict_of_ae hnn),
    canonicalHaarL1_limit_abs_cylinder_integral L hL,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem canonicalSyracuseMeasure_absolutelyContinuous_padicThreeHaar :
    canonicalSyracuseMeasure ≪ padicThreeHaar := by
  obtain ⟨L, hL⟩ := exists_canonicalHaarL1_limit
  rw [canonicalSyracuseMeasure_eq_withDensity_abs_limit L hL]
  exact withDensity_absolutelyContinuous _ _

/-- Taking the nonnegative representative loses no L1 error. -/
theorem canonicalHaarL1_limit_abs_error_eq_dist
    (L : ℤ_[3] →₁[padicThreeHaar] ℝ)
    (hL : Tendsto canonicalHaarL1 atTop (𝓝 L)) (n : ℕ) :
    (∫ x : ℤ_[3], |canonicalPadicRho n x - (|L x|)| ∂padicThreeHaar) =
      dist L (canonicalHaarL1 n) := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [canonicalHaarL1_coe n, canonicalHaarL1_limit_abs_ae L hL] with x hn hAbs
  rw [hn, hAbs, Real.dist_eq, abs_sub_comm]

theorem canonicalSyracuseMeasure_eq_withDensity_canonicalHaarDensity :
    canonicalSyracuseMeasure =
      padicThreeHaar.withDensity (fun x => ENNReal.ofReal (canonicalHaarDensity x)) :=
  canonicalSyracuseMeasure_eq_withDensity_abs_limit canonicalHaarLimit canonicalHaarLimit_tendsto

#print axioms canonicalSyracuseMeasure_eq_withDensity_abs_limit
#print axioms canonicalSyracuseMeasure_eq_withDensity_canonicalHaarDensity
#print axioms canonicalSyracuseMeasure_absolutelyContinuous_padicThreeHaar

end Erdos1135.Tao
