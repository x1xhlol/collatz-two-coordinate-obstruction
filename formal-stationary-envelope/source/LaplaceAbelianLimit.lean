import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology Set MeasureTheory

namespace CollatzCanonical.LaplaceAbelian

theorem exponential_first_moment_integrable :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  norm_num at h
  exact h

theorem exponential_first_moment :
    (∫ u : ℝ in Ioi 0, Real.exp (-u) * u) = 1 := by
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  norm_num at h
  exact h.symm

theorem scaled_laplace_integral_tendsto {A : ℝ → ℝ} {D C : ℝ}
    (hA : Measurable A) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → |A t| ≤ C * (t + 1))
    (hlimit : Tendsto (fun t : ℝ => A t / t) atTop (𝓝 D)) :
    Tendsto (fun ε : ℝ => ∫ u : ℝ in Ioi 0,
      Real.exp (-u) * (ε * A (u / ε))) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let B : ℝ → ℝ := fun u => C * (Real.exp (-u) * (u + 1))
  have hB : Integrable B μ := by
    have h := (exponential_first_moment_integrable.add
      (integrableOn_exp_neg_Ioi 0)).const_mul C
    convert h using 1
    ext u
    dsimp [B]
    ring
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun u : ℝ => Real.exp (-u) * (ε * A (u / ε))) μ := by
    apply Eventually.of_forall
    intro ε
    exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
      (measurable_const.mul (hA.comp (measurable_id.div_const ε)))).aestronglyMeasurable
  have hεlim : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    hεlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hdom : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ u : ℝ ∂μ,
      ‖Real.exp (-u) * (ε * A (u / ε))‖ ≤ B u := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε1 hε
    have hεpos : 0 < ε := hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hscaled : ε * |A (u / ε)| ≤ C * (u + 1) := by
      calc
        ε * |A (u / ε)| ≤ ε * (C * (u / ε + 1)) :=
          mul_le_mul_of_nonneg_left (hbound _ (div_nonneg hu0.le hεpos.le)) hεpos.le
        _ = C * (u + ε) := by field_simp [hεpos.ne']
        _ ≤ C * (u + 1) := mul_le_mul_of_nonneg_left (by linarith) hC
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_mul, abs_of_pos hεpos]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hscaled (Real.exp_pos (-u)).le]
  have hpoint : ∀ᵐ u : ℝ ∂μ,
      Tendsto (fun ε : ℝ => Real.exp (-u) * (ε * A (u / ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (D * (Real.exp (-u) * u))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hdiv : Tendsto (fun ε : ℝ => u / ε) (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [div_eq_mul_inv] using
        (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hu0
    have h := (hlimit.comp hdiv).const_mul (Real.exp (-u) * u)
    rw [mul_comm (Real.exp (-u) * u) D] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    dsimp
    field_simp [hu0.ne', hεpos.ne']
  have h := tendsto_integral_filter_of_dominated_convergence B hmeas hdom hB hpoint
  have hvalue : (∫ u : ℝ in Ioi 0, D * (Real.exp (-u) * u)) = D := by
    rw [integral_const_mul, exponential_first_moment, mul_one]
  simpa only [μ, hvalue] using h

theorem laplace_scaling_identity (A : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε ^ 2 * (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * A t) =
      ∫ u : ℝ in Ioi 0, Real.exp (-u) * (ε * A (u / ε)) := by
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.exp (-u) * (ε * A (u / ε))) 0 hε
  simp only [mul_zero, smul_eq_mul] at h
  have heq : (fun t : ℝ => Real.exp (-(ε * t)) * (ε * A (ε * t / ε))) =
      (fun t : ℝ => ε * (Real.exp (-(ε * t)) * A t)) := by
    ext t
    rw [mul_div_cancel_left₀ _ hε.ne']
    ring
  rw [heq, integral_const_mul] at h
  calc
    ε ^ 2 * (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * A t) =
        ε * (ε * (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * A t)) := by ring
    _ = ε * (ε⁻¹ * (∫ u : ℝ in Ioi 0, Real.exp (-u) * (ε * A (u / ε)))) := by rw [h]
    _ = _ := by field_simp [hε.ne']

/-- A linear mean at infinity determines the normalized Laplace limit. -/
theorem laplace_abelian_limit {A : ℝ → ℝ} {D C : ℝ}
    (hA : Measurable A) (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → |A t| ≤ C * (t + 1))
    (hlimit : Tendsto (fun t : ℝ => A t / t) atTop (𝓝 D)) :
    Tendsto (fun ε : ℝ => ε ^ 2 *
      (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * A t))
      (𝓝[>] (0 : ℝ)) (𝓝 D) := by
  apply (scaled_laplace_integral_tendsto hA hC hbound hlimit).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (laplace_scaling_identity A hε).symm

#print axioms exponential_first_moment_integrable
#print axioms exponential_first_moment
#print axioms scaled_laplace_integral_tendsto
#print axioms laplace_scaling_identity
#print axioms laplace_abelian_limit

end CollatzCanonical.LaplaceAbelian
