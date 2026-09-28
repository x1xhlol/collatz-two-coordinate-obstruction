import ComponentPositivityEquivalences
import NaturalLabelLimitIdentification

set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.LabelLaw CollatzCanonical.NaturalPrefix
open CollatzCanonical.DirichletAbelian
attribute [local instance] Classical.propDecidable

theorem natural_label_subset_mass_tendsto {I : Type*} {L : ℕ → LabelVector I}
    {p : LabelVector I} (h : Tendsto L atTop (𝓝 p)) (S : Set I) :
    Tendsto (fun X => labelSubsetMass S (L X)) atTop (𝓝 (labelSubsetMass S p)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun X => ?_))
    (tendsto_iff_norm_sub_tendsto_zero.mp h)
  exact labelSubsetMass_difference_le_fullL1 S (L X) p

theorem natural_label_subset_mass_eq {I : Type*} (F : ℕ → I) (S : Set I) (X : ℕ) :
    labelSubsetMass S (naturalFullLabelLaw F X) =
      (∑ q ∈ Finset.range X, if F (q + 1) ∈ S then (1 : ℝ) else 0) / (X : ℝ) := by
  unfold naturalFullLabelLaw fullNaturalPrefixSum
  rw [labelSubsetMass_smul, labelSubsetMass_finset_sum]
  simp_rw [Function.comp_apply, labelSubsetMass_atom]
  ring

theorem actual_component_natural_density (n : ℕ) :
    Tendsto (fun X : ℕ => (∑ q ∈ Finset.range X, componentIndicator n (q + 1)) / (X : ℝ))
      atTop (𝓝 (actualComponentMass n)) := by
  have hfull := (natural_label_limits_of_full_logarithmic_limit shortcutTailLabel
    shortcut_tail_label_passage_invariant (fun q _ => shortcutTailLabel_halving q)
    actualShortcutTailLaw actualShortcutTailLaw_spec.2.2).2
  have h := natural_label_subset_mass_tendsto hfull {shortcutTailLabel n}
  rw [labelSubsetMass_singleton] at h
  change Tendsto _ atTop (𝓝 (actualComponentMass n)) at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun X => by
    dsimp only
    rw [natural_label_subset_mass_eq]
    simp only [Set.mem_singleton_iff, shortcutTailLabel_eq_iff, componentIndicator])

theorem actual_component_logarithmic_and_natural_density_positive {n : ℕ} (hn : 0 < n) :
    0 < actualComponentMass n ∧
      Tendsto (fun t : ℝ => logarithmicCumulative (componentIndicator n) t / t)
        atTop (𝓝 (actualComponentMass n)) ∧
      Tendsto (fun X : ℕ => (∑ q ∈ Finset.range X, componentIndicator n (q + 1)) / (X : ℝ))
        atTop (𝓝 (actualComponentMass n)) :=
  ⟨actual_component_mass_positive hn, actual_component_logarithmic_mean n,
    actual_component_natural_density n⟩

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.natural_label_subset_mass_tendsto
#print axioms CollatzCanonical.ForwardComponent.natural_label_subset_mass_eq
#print axioms CollatzCanonical.ForwardComponent.actual_component_natural_density
#print axioms CollatzCanonical.ForwardComponent.actual_component_logarithmic_and_natural_density_positive
