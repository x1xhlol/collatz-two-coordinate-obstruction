import ComponentWholeOrbitWeight
import FixedBasinGreenBoundary
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian CollatzCanonical.Correction
open CollatzCanonical.GreenKernelScalars

theorem logarithmicCumulative_div_const (w : ℕ → ℝ) (c t : ℝ) :
    logarithmicCumulative (fun q => w q / c) t = logarithmicCumulative w t / c := by
  unfold logarithmicCumulative
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem logarithmicMean_div_const {w : ℕ → ℝ} {a : ℝ}
    (h : Tendsto (fun t => logarithmicCumulative w t / t) atTop (𝓝 a)) (c : ℝ) :
    Tendsto (fun t => logarithmicCumulative (fun q => w q / c) t / t)
      atTop (𝓝 (a / c)) := by
  apply (h.div_const c).congr'
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [logarithmicCumulative_div_const]
  ring

theorem tendsto_of_approximating_bounds {f : ℝ → ℝ} {lo hi : ℕ → ℝ → ℝ}
    {a b : ℕ → ℝ} {d : ℝ}
    (hlo : ∀ j, Tendsto (lo j) atTop (𝓝 (a j)))
    (hhi : ∀ j, Tendsto (hi j) atTop (𝓝 (b j)))
    (ha : Tendsto a atTop (𝓝 d)) (hb : Tendsto b atTop (𝓝 d))
    (hbound : ∀ j, ∀ᶠ t : ℝ in atTop, lo j t ≤ f t ∧ f t ≤ hi j t) :
    Tendsto f atTop (𝓝 d) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    obtain ⟨j, hj⟩ := (ha.eventually_const_lt hx).exists
    filter_upwards [(hlo j).eventually_const_lt hj, hbound j] with t ht hbt
    exact ht.trans_le hbt.1
  · intro x hx
    obtain ⟨j, hj⟩ := (hb.eventually_lt_const hx).exists
    filter_upwards [(hhi j).eventually_lt_const hj, hbound j] with t ht hbt
    exact hbt.2.trans_lt ht

noncomputable def truncatedComponentDensity (n j : ℕ) : ℝ :=
  actualFirstHitDensity (iterate j n) / wholeOrbitCorrection (iterate j n)

noncomputable def componentWeightedDensity (n : ℕ) : ℝ := ⨆ j, truncatedComponentDensity n j

theorem truncatedComponentWeight_logarithmic_mean {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (j : ℕ) :
    Tendsto (fun t => logarithmicCumulative (truncatedComponentWeight n j) t / t)
      atTop (𝓝 (truncatedComponentDensity n j)) := by
  have he : truncatedComponentWeight n j = fun q => firstHitWeight (iterate j n) q /
      wholeOrbitCorrection (iterate j n) := funext (truncatedComponentWeight_eq_firstHit hn hinj j)
  rw [he]
  exact logarithmicMean_div_const (actual_firstHitWeight_full_mean (iterate j n)) _

theorem truncatedComponentDensity_monotone {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) : Monotone (truncatedComponentDensity n) := by
  intro i j hij
  exact logarithmicMean_mono (truncatedComponentWeight_logarithmic_mean hn hinj i)
    (truncatedComponentWeight_logarithmic_mean hn hinj j)
    (fun q _ => truncatedComponentWeight_monotone hn hinj q hij)

theorem truncatedComponentDensity_bounds {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (j : ℕ) :
    0 ≤ truncatedComponentDensity n j ∧ truncatedComponentDensity n j ≤ actualComponentMass n := by
  constructor
  · exact logarithmicMean_nonneg (truncatedComponentWeight_logarithmic_mean hn hinj j)
      (fun q => (truncatedComponentWeight_bounds hn hinj j q).1)
  · exact logarithmicMean_mono (truncatedComponentWeight_logarithmic_mean hn hinj j)
      (actual_component_logarithmic_mean n) (fun q _ =>
        ((truncatedComponentWeight_bounds hn hinj j q).2).trans
          (componentOrbitWeight_bounds hn hinj q).2)

theorem truncatedComponentDensity_tendsto {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    Tendsto (truncatedComponentDensity n) atTop (𝓝 (componentWeightedDensity n)) := by
  apply tendsto_atTop_ciSup (truncatedComponentDensity_monotone hn hinj)
  exact ⟨actualComponentMass n, by rintro _ ⟨j, rfl⟩; exact (truncatedComponentDensity_bounds hn hinj j).2⟩

theorem actual_component_weighted_logarithmic_mean {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    Tendsto (fun t => logarithmicCumulative (componentOrbitWeight n) t / t)
      atTop (𝓝 (componentWeightedDensity n)) := by
  let lo : ℕ → ℝ → ℝ := fun j t => logarithmicCumulative (truncatedComponentWeight n j) t / t
  let hi : ℕ → ℝ → ℝ := fun j t => lo j t +
    logarithmicCumulative (componentIndicator n) t / t -
      logarithmicCumulative (basinIndicator (iterate j n)) t / t
  have hlo : ∀ j, Tendsto (lo j) atTop (𝓝 (truncatedComponentDensity n j)) :=
    truncatedComponentWeight_logarithmic_mean hn hinj
  have hhi : ∀ j, Tendsto (hi j) atTop
      (𝓝 (truncatedComponentDensity n j + actualComponentMass n - actualBasinDensity (iterate j n))) := by
    intro j
    exact ((hlo j).add (actual_component_logarithmic_mean n)).sub
      (actual_basin_full_logarithmic_mean (iterate j n))
  have ha := truncatedComponentDensity_tendsto hn hinj
  have hb : Tendsto (fun j => truncatedComponentDensity n j + actualComponentMass n -
      actualBasinDensity (iterate j n)) atTop (𝓝 (componentWeightedDensity n)) := by
    simpa only [add_sub_cancel_right] using
      (ha.add_const (actualComponentMass n)).sub (actual_forward_basin_density_tendsto_component_mass n)
  apply tendsto_of_approximating_bounds hlo hhi ha hb
  intro j
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  constructor
  · exact div_le_div_of_nonneg_right
      (logarithmicCumulative_le_of_positive_weights
        (fun q _ => (truncatedComponentWeight_bounds hn hinj j q).2) t) ht
  · have hp : ∀ q : ℕ, 0 < q → componentOrbitWeight n q ≤
        truncatedComponentWeight n j q + componentIndicator n q - basinIndicator (iterate j n) q := by
      intro q _
      have h := component_weight_truncation_error hn hinj j q
      linarith
    have h := div_le_div_of_nonneg_right (logarithmicCumulative_le_of_positive_weights hp t) ht
    simpa only [logarithmicCumulative_sub, logarithmicCumulative_add, sub_div, add_div] using h

theorem actual_firstHitDensity_forward_tendsto {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    Tendsto (fun j => actualFirstHitDensity (iterate j n)) atTop (𝓝 (componentWeightedDensity n)) := by
  have h := (truncatedComponentDensity_tendsto hn hinj).mul
    (wholeOrbitCorrection_forward_tendsto_one hn hinj)
  simp only [mul_one] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro j
  have hi := shortcut_component_injective
    (ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate n j)) hinj
  have hp := wholeOrbitCorrection_one_le (iterate_pos j hn) hi
  have hne : wholeOrbitCorrection (iterate j n) ≠ 0 := by linarith
  exact div_mul_cancel₀ _ hne

theorem componentWeightedDensity_bounds {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    0 ≤ componentWeightedDensity n ∧ componentWeightedDensity n ≤ actualComponentMass n := by
  constructor
  · exact logarithmicMean_nonneg (actual_component_weighted_logarithmic_mean hn hinj)
      (fun q => (componentOrbitWeight_bounds hn hinj q).1)
  · exact logarithmicMean_mono (actual_component_weighted_logarithmic_mean hn hinj)
      (actual_component_logarithmic_mean n) (fun q _ => (componentOrbitWeight_bounds hn hinj q).2)

theorem exists_uniform_componentWeightedDensity_comparison :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ n : ℕ, 0 < n → Function.Injective (fun i => iterate i n) →
      actualComponentMass n / P ≤ componentWeightedDensity n ∧
        componentWeightedDensity n ≤ actualComponentMass n := by
  obtain ⟨P, hP, hb⟩ := exists_uniform_wholeOrbitCorrection_bound
  refine ⟨P, hP, ?_⟩
  intro n hn hinj
  refine ⟨?_, (componentWeightedDensity_bounds hn hinj).2⟩
  exact logarithmicMean_mono (logarithmicMean_div_const (actual_component_logarithmic_mean n) P)
    (actual_component_weighted_logarithmic_mean hn hinj)
    (fun q _ => componentOrbitWeight_lower_bound hb hn hinj q)

theorem actual_green_ratio_forward_tendsto {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) :
    Tendsto (fun j => actualDensityValue actualFirstHitDensity (iterate j n) / (iterate j n : ℝ))
      atTop (𝓝 (delta * componentWeightedDensity n)) := by
  apply ((actual_firstHitDensity_forward_tendsto hn hinj).const_mul delta).congr'
  apply Filter.Eventually.of_forall
  intro j
  symm
  apply green_density_ratio_of_nonperiodic (iterate_pos j hn)
  rintro ⟨r, hr, hret⟩
  exact shortcut_component_target_nonperiodic
    (ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate n j)) hinj r hr hret

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.actual_component_weighted_logarithmic_mean
#print axioms CollatzCanonical.ForwardComponent.actual_firstHitDensity_forward_tendsto
#print axioms CollatzCanonical.ForwardComponent.actual_green_ratio_forward_tendsto
#print axioms CollatzCanonical.ForwardComponent.exists_uniform_componentWeightedDensity_comparison
