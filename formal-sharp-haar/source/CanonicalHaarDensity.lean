import CanonicalHaarTwoScale

/-!
# A concrete nonnegative Haar density from the canonical L1 limit

The representative is chosen only after existence of the L1 limit has been
proved. Taking its absolute value gives a globally nonnegative function
without changing the limiting error bounds.
-/

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

noncomputable def canonicalHaarLimit : ℤ_[3] →₁[padicThreeHaar] ℝ :=
  Classical.choose exists_canonicalHaarL1_limit

theorem canonicalHaarLimit_tendsto :
    Tendsto canonicalHaarL1 atTop (𝓝 canonicalHaarLimit) :=
  Classical.choose_spec exists_canonicalHaarL1_limit

noncomputable def canonicalHaarDensity (x : ℤ_[3]) : ℝ := |canonicalHaarLimit x|

theorem canonicalHaarDensity_nonneg (x : ℤ_[3]) : 0 ≤ canonicalHaarDensity x :=
  abs_nonneg _

theorem canonicalHaarDensity_integrable : Integrable canonicalHaarDensity padicThreeHaar :=
  (L1.integrable_coeFn canonicalHaarLimit).abs

theorem canonicalHaarL1_norm (n : ℕ) : ‖canonicalHaarL1 n‖ = 1 := by
  rw [canonicalHaarL1, L1.norm_of_fun_eq_integral_norm]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (canonicalPadicRho_nonneg n _)]
  exact canonicalPadicRho_integral n

theorem canonicalHaarDensity_integral :
    (∫ x : ℤ_[3], canonicalHaarDensity x ∂padicThreeHaar) = 1 := by
  have hn : ‖canonicalHaarLimit‖ = 1 :=
    tendsto_nhds_unique canonicalHaarLimit_tendsto.norm
      (by simpa only [canonicalHaarL1_norm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  rw [L1.norm_eq_integral_norm] at hn
  simpa only [Real.norm_eq_abs, canonicalHaarDensity] using hn

theorem canonicalHaarDensity_error_le_dist (m : ℕ) :
    (∫ x : ℤ_[3], |canonicalPadicRho m x - canonicalHaarDensity x| ∂padicThreeHaar) ≤
      dist canonicalHaarLimit (canonicalHaarL1 m) := by
  rw [dist_comm, L1.dist_eq_integral_dist]
  have heq : (∫ x : ℤ_[3], dist (canonicalHaarL1 m x) (canonicalHaarLimit x)
      ∂padicThreeHaar) =
      ∫ x : ℤ_[3], |canonicalPadicRho m x - canonicalHaarLimit x| ∂padicThreeHaar := by
    apply integral_congr_ae
    filter_upwards [canonicalHaarL1_coe m] with x hx
    rw [hx, Real.dist_eq]
  rw [heq]
  apply integral_mono
    ((canonicalPadicRho_integrable padicThreeHaar m).sub canonicalHaarDensity_integrable).abs
    ((canonicalPadicRho_integrable padicThreeHaar m).sub
      (L1.integrable_coeFn canonicalHaarLimit)).abs
  intro x
  change |canonicalPadicRho m x - abs (canonicalHaarLimit x)| ≤ _
  simpa only [abs_of_nonneg (canonicalPadicRho_nonneg m x)] using
    (abs_abs_sub_abs_le_abs_sub (canonicalPadicRho m x) (canonicalHaarLimit x))

theorem exists_canonicalHaarDensity_polynomial_rate (A : ℕ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
      (∫ x : ℤ_[3], |canonicalPadicRho m x - canonicalHaarDensity x| ∂padicThreeHaar) ≤
        C / (m : ℝ)^A := by
  obtain ⟨C, hC, hbound⟩ :=
    canonicalHaarL1_limit_polynomial_rate canonicalHaarLimit canonicalHaarLimit_tendsto A hA
  exact ⟨C, hC, fun m hm => (canonicalHaarDensity_error_le_dist m).trans (hbound m hm)⟩

theorem canonicalHaarDensity_L1_tendsto :
    Tendsto (fun m : ℕ => ∫ x : ℤ_[3],
      |canonicalPadicRho m x - canonicalHaarDensity x| ∂padicThreeHaar) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_canonicalHaarDensity_polynomial_rate 1 (by omega)
  apply squeeze_zero'
    (Eventually.of_forall fun m => integral_nonneg fun x => abs_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    simpa only [pow_one] using hbound m hm
  · exact tendsto_const_div_atTop_nhds_zero_nat C

#print axioms canonicalHaarDensity_integral
#print axioms exists_canonicalHaarDensity_polynomial_rate
#print axioms canonicalHaarDensity_L1_tendsto

end Erdos1135.Tao
