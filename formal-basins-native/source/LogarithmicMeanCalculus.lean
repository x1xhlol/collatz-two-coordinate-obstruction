import BasinWeightedDensityComparison

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.DirichletAbelian
open CollatzCylinderPacking.Arithmetic

theorem logarithmicCumulative_add (w v : ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative (fun q => w q + v q) t =
      logarithmicCumulative w t + logarithmicCumulative v t := by
  unfold logarithmicCumulative
  simp_rw [add_div]
  exact Finset.sum_add_distrib

theorem logarithmicCumulative_sub (w v : ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative (fun q => w q - v q) t =
      logarithmicCumulative w t - logarithmicCumulative v t := by
  unfold logarithmicCumulative
  simp_rw [sub_div]
  rw [Finset.sum_sub_distrib]

theorem logarithmicMean_mono {w v : ℕ → ℝ} {a b : ℝ}
    (hw : Tendsto (fun t => logarithmicCumulative w t / t) atTop (𝓝 a))
    (hv : Tendsto (fun t => logarithmicCumulative v t / t) atTop (𝓝 b))
    (h : ∀ q : ℕ, 0 < q → w q ≤ v q) : a ≤ b := by
  apply le_of_tendsto_of_tendsto hw hv
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact div_le_div_of_nonneg_right (logarithmicCumulative_le_of_positive_weights h t) ht

theorem logarithmicMean_nonneg {w : ℕ → ℝ} {a : ℝ}
    (hw : Tendsto (fun t => logarithmicCumulative w t / t) atTop (𝓝 a))
    (h : ∀ q : ℕ, 0 ≤ w q) : 0 ≤ a := by
  apply ge_of_tendsto hw
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact div_nonneg (logarithmicCumulative_nonneg h t) ht

end CollatzCanonical.DirichletAbelian
