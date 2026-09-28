import ComponentWeightedMean

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.GreenKernelScalars

theorem componentOrbitWeight_eq_of_related {n m : ℕ} (h : ShortcutTailRelated n m) :
    componentOrbitWeight n = componentOrbitWeight m := by
  funext q
  have he : ShortcutTailRelated q n ↔ ShortcutTailRelated q m :=
    ⟨fun hq => ShortcutTailRelated_equivalence.trans hq h,
      fun hq => ShortcutTailRelated_equivalence.trans hq (ShortcutTailRelated_equivalence.symm h)⟩
  unfold componentOrbitWeight
  rw [he]

theorem componentWeightedDensity_eq_of_related {n m : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n)) (h : ShortcutTailRelated n m) :
    componentWeightedDensity n = componentWeightedDensity m := by
  have hmn := ShortcutTailRelated_equivalence.symm h
  have hm := shortcut_component_positive hn hmn
  have him := shortcut_component_injective hmn hinj
  have hl := actual_component_weighted_logarithmic_mean hn hinj
  rw [componentOrbitWeight_eq_of_related h] at hl
  exact tendsto_nhds_unique hl (actual_component_weighted_logarithmic_mean hm him)

theorem exists_uniform_forward_component_ratio_bounds :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ n : ℕ, 0 < n → Function.Injective (fun i => iterate i n) →
      delta / P * actualComponentMass n ≤ delta * componentWeightedDensity n ∧
        delta * componentWeightedDensity n ≤ delta * actualComponentMass n := by
  obtain ⟨P, hP, hbound⟩ := exists_uniform_componentWeightedDensity_comparison
  refine ⟨P, hP, ?_⟩
  intro n hn hinj
  obtain ⟨hlo, hhi⟩ := hbound n hn hinj
  constructor
  · calc
      delta / P * actualComponentMass n = delta * (actualComponentMass n / P) := by ring
      _ ≤ delta * componentWeightedDensity n := mul_le_mul_of_nonneg_left hlo delta_pos.le
  · exact mul_le_mul_of_nonneg_left hhi delta_pos.le

theorem actual_forward_component_mass_and_ratio :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ n : ℕ, 0 < n → Function.Injective (fun i => iterate i n) →
      Tendsto (fun j => actualBasinDensity (iterate j n)) atTop (𝓝 (actualComponentMass n)) ∧
      Tendsto (fun j => actualFirstHitDensity (iterate j n)) atTop (𝓝 (componentWeightedDensity n)) ∧
      Tendsto (fun j => actualDensityValue actualFirstHitDensity (iterate j n) / (iterate j n : ℝ))
        atTop (𝓝 (delta * componentWeightedDensity n)) ∧
      delta / P * actualComponentMass n ≤ delta * componentWeightedDensity n ∧
        delta * componentWeightedDensity n ≤ delta * actualComponentMass n := by
  obtain ⟨P, hP, hbound⟩ := exists_uniform_forward_component_ratio_bounds
  refine ⟨P, hP, ?_⟩
  intro n hn hinj
  exact ⟨actual_forward_basin_density_tendsto_component_mass n,
    actual_firstHitDensity_forward_tendsto hn hinj, actual_green_ratio_forward_tendsto hn hinj,
    hbound n hn hinj⟩

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.componentWeightedDensity_eq_of_related
#print axioms CollatzCanonical.ForwardComponent.actual_forward_component_mass_and_ratio
