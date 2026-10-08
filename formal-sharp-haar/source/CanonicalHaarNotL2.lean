import CanonicalHaarLp
import CanonicalHaarStationarity
import PadicHaarLift
import StationarySupportOverlap

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

private theorem oddLift_memLp_two {f : ℤ_[3] → ℝ} (hf : MemLp f 2 padicThreeHaar) :
    MemLp (padicOddLift f) 2 padicThreeHaar := by
  have hfi := (padicOddLift_integrable_iff f).mpr (MemLp.integrable (by norm_num) hf)
  apply (memLp_two_iff_integrable_sq hfi.aestronglyMeasurable).mpr
  rw [padicOddLift_comp_zero f (fun y : ℝ => y ^ 2) (by norm_num)]
  exact (padicOddLift_integrable_iff _).mpr hf.integrable_sq

private theorem half_doubling_support (f : ℤ_[3] → ℝ) :
    padicThreeHaar {x | 0 < (1 / 2 : ℝ) * f (2 * x)} =
      padicThreeHaar {x | 0 < f x} := by
  have hsets : {x : ℤ_[3] | 0 < (1 / 2 : ℝ) * f (2 * x)} =
      (fun x : ℤ_[3] => 2 * x) ⁻¹' {x | 0 < f x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor <;> intro h <;> linarith
  rw [hsets]
  exact padicThreeHaar_doubling_preserving.measure_preimage_emb
    padicThree_doubling_measurableEmbedding _

private theorem half_doubling_sq_integral (f : ℤ_[3] → ℝ) :
    (∫ x : ℤ_[3], ((1 / 2 : ℝ) * f (2 * x)) ^ 2 ∂padicThreeHaar) =
      (1 / 4 : ℝ) * ∫ x : ℤ_[3], (f x) ^ 2 ∂padicThreeHaar := by
  simp_rw [mul_pow]
  rw [integral_const_mul,
    padicThreeHaar_doubling_preserving.integral_comp
      padicThree_doubling_measurableEmbedding (fun x => (f x) ^ 2)]
  norm_num

private theorem three_halves_lift_sq_integral (f : ℤ_[3] → ℝ) :
    (∫ x : ℤ_[3], ((3 / 2 : ℝ) * padicOddLift f x) ^ 2 ∂padicThreeHaar) =
      (3 / 4 : ℝ) * ∫ x : ℤ_[3], (f x) ^ 2 ∂padicThreeHaar := by
  simp_rw [mul_pow]
  rw [integral_const_mul,
    padicOddLift_comp_zero f (fun y : ℝ => y ^ 2) (by norm_num), padicOddLift_integral]
  ring

private theorem canonicalHaarDensity_not_memLp_two_of_stationary
    (hstationary : canonicalHaarDensity =ᵐ[padicThreeHaar] fun x =>
      (1 / 2 : ℝ) * canonicalHaarDensity (2 * x) +
        (3 / 2 : ℝ) * padicOddLift canonicalHaarDensity x) :
    ¬ MemLp canonicalHaarDensity 2 padicThreeHaar := by
  intro hf
  let a : ℤ_[3] → ℝ := fun x => (1 / 2 : ℝ) * canonicalHaarDensity (2 * x)
  let b : ℤ_[3] → ℝ := fun x => (3 / 2 : ℝ) * padicOddLift canonicalHaarDensity x
  have ha : MemLp a 2 padicThreeHaar :=
    (hf.comp_measurePreserving padicThreeHaar_doubling_preserving).const_mul (1 / 2)
  have hb : MemLp b 2 padicThreeHaar := (oddLift_memLp_two hf).const_mul (3 / 2)
  have ha_nonneg : 0 ≤ᵐ[padicThreeHaar] a := ae_of_all _ fun x =>
    mul_nonneg (by norm_num) (canonicalHaarDensity_nonneg (2 * x))
  have hb_nonneg : 0 ≤ᵐ[padicThreeHaar] b := ae_of_all _ fun x =>
    mul_nonneg (by norm_num) (padicOddLift_nonneg canonicalHaarDensity_nonneg x)
  have hb_pos : 0 < ∫ x : ℤ_[3], b x ∂padicThreeHaar := by
    change 0 < ∫ x : ℤ_[3], (3 / 2 : ℝ) * padicOddLift canonicalHaarDensity x ∂padicThreeHaar
    rw [integral_const_mul, padicOddLift_integral, canonicalHaarDensity_integral]
    norm_num
  have hcritical : (∫ x : ℤ_[3], (canonicalHaarDensity x) ^ 2 ∂padicThreeHaar) =
      (∫ x : ℤ_[3], (a x) ^ 2 ∂padicThreeHaar) +
        ∫ x : ℤ_[3], (b x) ^ 2 ∂padicThreeHaar := by
    rw [show (∫ x : ℤ_[3], (a x) ^ 2 ∂padicThreeHaar) =
      (1 / 4 : ℝ) * ∫ x : ℤ_[3], (canonicalHaarDensity x) ^ 2 ∂padicThreeHaar from
        half_doubling_sq_integral _,
      show (∫ x : ℤ_[3], (b x) ^ 2 ∂padicThreeHaar) =
      (3 / 4 : ℝ) * ∫ x : ℤ_[3], (canonicalHaarDensity x) ^ 2 ∂padicThreeHaar from
        three_halves_lift_sq_integral _]
    ring
  exact critical_sq_identity_impossible padicThreeHaar ha hb ha_nonneg hb_nonneg
    hstationary (half_doubling_support canonicalHaarDensity) hb_pos hcritical

/-- The actual canonical Haar density fails at the critical exponent. -/
theorem canonicalHaarDensity_not_memLp_two :
    ¬ MemLp canonicalHaarDensity 2 padicThreeHaar :=
  canonicalHaarDensity_not_memLp_two_of_stationary canonicalHaarDensity_stationary

/-- Among real exponents at least one, the exact integrability threshold is two. -/
theorem canonicalHaarDensity_memLp_iff_lt_two {p : ℝ} (hp : 1 ≤ p) :
    MemLp canonicalHaarDensity (ENNReal.ofReal p) padicThreeHaar ↔ p < 2 := by
  constructor
  · intro hf
    by_contra hnot
    have hp2 : (2 : ℝ) ≤ p := le_of_not_gt hnot
    have h2p : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa using ENNReal.ofReal_le_ofReal hp2
    exact canonicalHaarDensity_not_memLp_two (hf.mono_exponent h2p)
  · exact canonicalHaarDensity_memLp_of_lt_two hp

/-- One nonnegative normalized density represents the canonical law and has the sharp Lp range. -/
theorem canonicalSyracuseMeasure_has_sharp_lp_density :
    ∃ f : ℤ_[3] → ℝ, (∀ x, 0 ≤ f x) ∧
      (∫ x, f x ∂padicThreeHaar) = 1 ∧
      canonicalSyracuseMeasure = padicThreeHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∀ p : ℝ, 1 ≤ p → (MemLp f (ENNReal.ofReal p) padicThreeHaar ↔ p < 2) :=
  ⟨canonicalHaarDensity, canonicalHaarDensity_nonneg, canonicalHaarDensity_integral,
    canonicalSyracuseMeasure_eq_withDensity_canonicalHaarDensity,
    fun _ hp => canonicalHaarDensity_memLp_iff_lt_two hp⟩

#print axioms canonicalHaarDensity_not_memLp_two
#print axioms canonicalHaarDensity_memLp_iff_lt_two
#print axioms canonicalSyracuseMeasure_has_sharp_lp_density

end Erdos1135.Tao
