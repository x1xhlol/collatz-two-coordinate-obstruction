import DirichletLaplaceIdentity
import LaplaceAbelianLimit
import DirichletSeriesReindex

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

open LaplaceAbelian

theorem laplace_linear_majorant_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * (t + 1)) (Ioi 0) := by
  have hscaled : IntegrableOn
      (fun t : ℝ => Real.exp (-(ε * t)) * (ε * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u) 0 hε).mpr
    simpa using exponential_first_moment_integrable
  have hfirst : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * t) (Ioi 0) := by
    apply (hscaled.mul_const ε⁻¹).congr
    filter_upwards with t
    field_simp [hε.ne']
  have hzero : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0
  apply (hfirst.add hzero).congr
  filter_upwards with t
  dsimp
  ring

theorem normalized_laplace_linear_majorant {ε : ℝ} (hε : 0 < ε) :
    ε ^ 2 * (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * (t + 1)) = 1 + ε := by
  rw [laplace_scaling_identity (fun t : ℝ => t + 1) hε]
  have heq : (fun u : ℝ => Real.exp (-u) * (ε * (u / ε + 1))) =
      (fun u : ℝ => Real.exp (-u) * u + ε * Real.exp (-u)) := by
    ext u
    field_simp [hε.ne']
  rw [heq, integral_add exponential_first_moment_integrable
    ((integrableOn_exp_neg_Ioi 0).const_mul ε), integral_const_mul,
    exponential_first_moment, integral_exp_neg_Ioi_zero, mul_one]

theorem logarithmicCumulative_laplace_integrable {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * logarithmicCumulative w t) (Ioi 0) := by
  apply (laplace_linear_majorant_integrable hε).mono'
  · exact ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).measurable.mul
      (logarithmicCumulative_measurable hw0)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (logarithmicCumulative_linear_bound hw0 hw1 (le_of_lt ht)) (Real.exp_pos _).le

theorem normalized_zeta_le {ε : ℝ} (hε : 0 < ε) :
    ε * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ)) ≤ 1 + ε := by
  have hidentity := dirichlet_laplace_identity
    (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) (fun _ => le_rfl) hε
  simp only [one_mul] at hidentity
  rw [hidentity, ← normalized_laplace_linear_majorant hε]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
  apply integral_mono_ae
    (logarithmicCumulative_laplace_integrable (fun _ => zero_le_one) (fun _ => le_rfl) hε)
    (laplace_linear_majorant_integrable hε)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact (le_abs_self _).trans
    (logarithmicCumulative_linear_bound (fun _ => zero_le_one) (fun _ => le_rfl) (le_of_lt ht))

theorem weighted_dirichlet_abelian_shifted {w : ℕ → ℝ} {D : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hmean : Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 D)) :
    Tendsto (fun ε : ℝ => ε *
      ∑' n : ℕ, w (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 D) := by
  have h := laplace_abelian_limit (logarithmicCumulative_measurable hw0)
    zero_le_one (fun t ht => by simpa only [one_mul] using
      logarithmicCumulative_linear_bound hw0 hw1 ht) hmean
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dirichlet_laplace_identity hw0 hw1 hε).symm

theorem powered_weighted_dirichlet_abelian_shifted {w : ℕ → ℝ} {D : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hmean : Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 D)) :
    Tendsto (fun ε : ℝ => ε *
      ∑' n : ℕ, w (n + 1) ^ (1 + ε) * ((n + 1 : ℕ) : ℝ) ^ (-1 - ε : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 D) :=
  powered_dirichlet_limit_of_normalized_zeta_bound hw0 hw1
    (fun _ hε => normalized_zeta_le hε) (weighted_dirichlet_abelian_shifted hw0 hw1 hmean)

/-- The logarithmic mean gives the full weighted Dirichlet residue. The sum is over
all natural numbers; its zero term is zero, while the integer 1 is retained. -/
theorem weighted_dirichlet_abelian {w : ℕ → ℝ} {D : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hmean : Tendsto (fun t : ℝ => logarithmicCumulative w t / t) atTop (𝓝 D)) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' q : ℕ, w q ^ s / (q : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 D) := by
  have h := (powered_weighted_dirichlet_abelian_shifted hw0 hw1 hmean).comp
    subtract_one_tendsto_nhdsGT
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 0 < s - 1 := sub_pos.mpr hs
  dsimp
  rw [powered_dirichlet_reindex hw0 hw1 hs1,
    show (1 : ℝ) + (s - 1) = s by ring]

#print axioms laplace_linear_majorant_integrable
#print axioms normalized_laplace_linear_majorant
#print axioms logarithmicCumulative_laplace_integrable
#print axioms normalized_zeta_le
#print axioms weighted_dirichlet_abelian_shifted
#print axioms powered_weighted_dirichlet_abelian_shifted
#print axioms weighted_dirichlet_abelian

end CollatzCanonical.DirichletAbelian
