import ShortcutMinimumCapture
import LabelLogarithmicDensity
import LogarithmicMeanCalculus
import StandardCollatzMinimumLaw

set_option autoImplicit false
open Filter
open scoped Topology ENNReal lp

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.LabelLaw CollatzCanonical.DirichletAbelian Erdos1135.Tao
attribute [local instance] Classical.propDecidable

noncomputable def actualShortcutTailLaw : LabelVector ShortcutTailComponent :=
  Classical.choose (actual_halving_invariant_label_law shortcutTailLabel
    shortcut_tail_label_passage_invariant (fun q _ => shortcutTailLabel_halving q))

theorem actualShortcutTailLaw_spec :
    IsProbabilityVector actualShortcutTailLaw ∧
      Tendsto (oddLabelLaw shortcutTailLabel) atTop (𝓝 actualShortcutTailLaw) ∧
      Tendsto (fullLabelLaw shortcutTailLabel) atTop (𝓝 actualShortcutTailLaw) :=
  Classical.choose_spec (actual_halving_invariant_label_law shortcutTailLabel
    shortcut_tail_label_passage_invariant (fun q _ => shortcutTailLabel_halving q))

noncomputable def actualShortcutTailPMF : PMF ShortcutTailComponent :=
  probabilityVectorPMF actualShortcutTailLaw actualShortcutTailLaw_spec.1

noncomputable def actualComponentMass (n : ℕ) : ℝ := actualShortcutTailLaw (shortcutTailLabel n)

theorem actualComponentMass_eq_PMF (n : ℕ) :
    actualComponentMass n = (actualShortcutTailPMF (shortcutTailLabel n)).toReal :=
  (probabilityVectorPMF_toReal _ _ _).symm

noncomputable def componentIndicator (n q : ℕ) : ℝ := if ShortcutTailRelated q n then 1 else 0

noncomputable def actualStandardMinimumLaw : LabelVector ℕ :=
  Classical.choose (actual_halving_invariant_label_law collatzOrbitMin
    standard_global_minimum_eventually_passage_invariant (fun _ hq => collatzOrbitMin_halving hq))

theorem actualStandardMinimumLaw_spec :
    IsProbabilityVector actualStandardMinimumLaw ∧
      Tendsto (oddLabelLaw collatzOrbitMin) atTop (𝓝 actualStandardMinimumLaw) ∧
      Tendsto (fullLabelLaw collatzOrbitMin) atTop (𝓝 actualStandardMinimumLaw) :=
  Classical.choose_spec (actual_halving_invariant_label_law collatzOrbitMin
    standard_global_minimum_eventually_passage_invariant (fun _ hq => collatzOrbitMin_halving hq))

noncomputable def minimumTailIndicator (M q : ℕ) : ℝ := if M < collatzOrbitMin q then 1 else 0

noncomputable def actualMinimumTailMass (M : ℕ) : ℝ :=
  labelSubsetMass {i : ℕ | M < i} actualStandardMinimumLaw

theorem actual_component_logarithmic_mean (n : ℕ) :
    Tendsto (fun t => logarithmicCumulative (componentIndicator n) t / t)
      atTop (𝓝 (actualComponentMass n)) := by
  have h := full_label_law_logarithmic_mean actualShortcutTailLaw_spec.2.2 {shortcutTailLabel n}
  simpa only [Set.mem_singleton_iff, shortcutTailLabel_eq_iff, labelSubsetMass_singleton,
    componentIndicator, actualComponentMass] using h

theorem actual_minimum_tail_logarithmic_mean (M : ℕ) :
    Tendsto (fun t => logarithmicCumulative (minimumTailIndicator M) t / t)
      atTop (𝓝 (actualMinimumTailMass M)) := by
  unfold actualMinimumTailMass
  apply (full_label_law_logarithmic_mean actualStandardMinimumLaw_spec.2.2
    {i : ℕ | M < i}).congr'
  apply Filter.Eventually.of_forall
  intro t
  apply congrArg (fun w : ℕ → ℝ => logarithmicCumulative w t / t)
  funext q
  unfold minimumTailIndicator
  simp only [Set.mem_setOf_eq]
  split_ifs <;> rfl

theorem actualMinimumTailMass_tendsto_zero :
    Tendsto actualMinimumTailMass atTop (𝓝 0) :=
  probability_vector_nat_tail_tendsto_zero actualStandardMinimumLaw

theorem actualComponentMass_bounds (n : ℕ) :
    0 ≤ actualComponentMass n ∧ actualComponentMass n ≤ 1 := by
  exact ⟨actualShortcutTailLaw_spec.1.1 _,
    by simpa only [labelSubsetMass_singleton] using
      labelSubsetMass_le_one actualShortcutTailLaw_spec.1 {shortcutTailLabel n}⟩

theorem actualComponentMass_eq_of_related {q n : ℕ} (h : ShortcutTailRelated q n) :
    actualComponentMass q = actualComponentMass n := by
  unfold actualComponentMass
  rw [(shortcutTailLabel_eq_iff q n).mpr h]

theorem basinIndicator_le_componentIndicator (n q : ℕ) :
    basinIndicator n q ≤ componentIndicator n q := by
  by_cases h : ∃ a, iterate a q = n
  · obtain ⟨a, ha⟩ := h
    have hc : ShortcutTailRelated q n := ⟨a, 0, ha⟩
    simp only [componentIndicator, if_pos hc]
    exact (basinIndicator_bounds n q).2
  · simp only [basinIndicator, if_neg h, componentIndicator]
    split_ifs <;> norm_num

theorem actualBasinDensity_le_component_mass (n : ℕ) :
    actualBasinDensity n ≤ actualComponentMass n :=
  logarithmicMean_mono (actual_basin_full_logarithmic_mean n)
    (actual_component_logarithmic_mean n) (fun q _ => basinIndicator_le_componentIndicator n q)

theorem spine_basin_indicator_gap_bound (n M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ q : ℕ, 0 < q →
      componentIndicator n q ≤ basinIndicator (iterate j n) q + minimumTailIndicator M q := by
  obtain ⟨J, hJ⟩ := shortcut_component_spine_error_subset_minimum_tail n M
  refine ⟨J, ?_⟩
  intro j hj q hq
  by_cases hc : ShortcutTailRelated q n
  · by_cases hb : ∃ a, iterate a q = iterate j n
    · simp only [componentIndicator, if_pos hc, basinIndicator, if_pos hb, minimumTailIndicator]
      split_ifs <;> norm_num
    · have hm := hJ j hj q hq hc hb
      simp only [componentIndicator, if_pos hc, basinIndicator, if_neg hb,
        minimumTailIndicator, if_pos hm]
      norm_num
  · simp only [componentIndicator, if_neg hc]
    exact add_nonneg (basinIndicator_bounds _ _).1 (by
      unfold minimumTailIndicator
      split_ifs <;> norm_num)

theorem spine_basin_density_gap_bound (n M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      actualComponentMass n ≤ actualBasinDensity (iterate j n) + actualMinimumTailMass M := by
  obtain ⟨J, hJ⟩ := spine_basin_indicator_gap_bound n M
  refine ⟨J, ?_⟩
  intro j hj
  have hsum := (actual_basin_full_logarithmic_mean (iterate j n)).add
    (actual_minimum_tail_logarithmic_mean M)
  have hsum' : Tendsto (fun t => logarithmicCumulative
      (fun q => basinIndicator (iterate j n) q + minimumTailIndicator M q) t / t)
      atTop (𝓝 (actualBasinDensity (iterate j n) + actualMinimumTailMass M)) := by
    simpa only [logarithmicCumulative_add, add_div] using hsum
  exact logarithmicMean_mono (actual_component_logarithmic_mean n) hsum' (hJ j hj)

theorem actual_forward_basin_density_tendsto_component_mass (n : ℕ) :
    Tendsto (fun j => actualBasinDensity (iterate j n)) atTop (𝓝 (actualComponentMass n)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := (actualMinimumTailMass_tendsto_zero.eventually_lt_const hε).exists
  obtain ⟨J, hJ⟩ := spine_basin_density_gap_bound n M
  refine ⟨J, ?_⟩
  intro j hj
  have hu : actualBasinDensity (iterate j n) ≤ actualComponentMass n := by
    rw [← actualComponentMass_eq_of_related
      (ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate n j))]
    exact actualBasinDensity_le_component_mass (iterate j n)
  have hl := hJ j hj
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.actual_component_logarithmic_mean
#print axioms CollatzCanonical.ForwardComponent.actualMinimumTailMass_tendsto_zero
#print axioms CollatzCanonical.ForwardComponent.actual_forward_basin_density_tendsto_component_mass
