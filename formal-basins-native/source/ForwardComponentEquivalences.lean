import ComponentRatioLimit
import PeriodicComponentMass

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.LabelLaw CollatzCanonical.GreenKernelScalars

def NonperiodicGreenSublinear : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ V : ℕ, ∀ v : ℕ, V < v →
    (¬ ∃ r : ℕ, 0 < r ∧ iterate r v = v) →
      |actualDensityValue actualFirstHitDensity v / (v : ℝ)| < ε

def DivergentTraceVanishes : Prop :=
  ∀ n : ℕ, Function.Injective (fun i => iterate i n) →
    actualDensityValue actualFirstHitDensity n = 0

theorem shortcut_injective_start_positive {n : ℕ}
    (hinj : Function.Injective (fun i => iterate i n)) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  have he : iterate 0 n = iterate 1 n := by rw [hn, shortcut_iterate_zero_start, shortcut_iterate_zero_start]
  have hbad := hinj he
  omega

theorem component_mass_zero_of_forward_green_ratio_zero {n : ℕ} (hn : 0 < n)
    (hinj : Function.Injective (fun i => iterate i n))
    (hz : Tendsto (fun j => actualDensityValue actualFirstHitDensity (iterate j n) / (iterate j n : ℝ))
      atTop (𝓝 0)) : actualComponentMass n = 0 := by
  have he : delta * componentWeightedDensity n = 0 :=
    tendsto_nhds_unique (actual_green_ratio_forward_tendsto hn hinj) hz
  obtain ⟨P, hP, hb⟩ := exists_uniform_forward_component_ratio_bounds
  have hlo := (hb n hn hinj).1
  rw [he] at hlo
  have hp : 0 < delta / P := div_pos delta_pos (by linarith)
  have hnonpos : actualComponentMass n ≤ 0 := by
    by_contra h
    exact (not_le_of_gt (mul_pos hp (by linarith : 0 < actualComponentMass n))) hlo
  exact le_antisymm hnonpos (actualComponentMass_bounds n).1

theorem divergent_trace_vanishes_of_null (hnull : DivergentComponentsNull) :
    DivergentTraceVanishes := by
  intro n hinj
  obtain ⟨_, _, hcompare⟩ := actual_basin_and_weighted_density_comparison
  have hD : actualFirstHitDensity n ≤ 0 := by
    have h := (hcompare n).1.trans (actualBasinDensity_le_component_mass n)
    simpa only [hnull n hinj] using h
  have he := le_antisymm hD (actualFirstHitDensity_nonneg n)
  simp only [actualDensityValue, he, mul_zero]

theorem divergent_components_null_of_trace_vanishes (hzero : DivergentTraceVanishes) :
    DivergentComponentsNull := by
  intro n hinj
  apply component_mass_zero_of_forward_green_ratio_zero (shortcut_injective_start_positive hinj) hinj
  have he : (fun j => actualDensityValue actualFirstHitDensity (iterate j n) / (iterate j n : ℝ)) =
      fun _ : ℕ => (0 : ℝ) := by
    funext j
    have hi := shortcut_component_injective
      (ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate n j)) hinj
    rw [hzero (iterate j n) hi, zero_div]
  rw [he]
  exact tendsto_const_nhds

theorem divergent_components_null_of_sublinear (hsmall : NonperiodicGreenSublinear) :
    DivergentComponentsNull := by
  intro n hinj
  apply component_mass_zero_of_forward_green_ratio_zero (shortcut_injective_start_positive hinj) hinj
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨V, hV⟩ := hsmall ε hε
  filter_upwards [(shortcut_divergent_spine_tendsto_atTop hinj).eventually_gt_atTop V] with j hj
  rw [Real.dist_eq, sub_zero]
  apply hV (iterate j n) hj
  rintro ⟨r, hr, hret⟩
  exact shortcut_component_target_nonperiodic
    (ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate n j)) hinj r hr hret

theorem nonperiodic_green_sublinear_of_null (hnull : DivergentComponentsNull) :
    NonperiodicGreenSublinear := by
  classical
  intro ε hε
  obtain ⟨s, hperiodic, hmass⟩ := periodic_components_finite_mass_approx hnull (div_pos hε delta_pos)
  have hcuts : ∀ C : ShortcutTailComponent, ∃ V : ℕ, ∀ v : ℕ, V < v → C ∈ s →
      shortcutTailLabel v = C → |actualDensityValue actualFirstHitDensity v / (v : ℝ)| < ε := by
    intro C
    by_cases hC : C ∈ s
    · obtain ⟨c, hc, hcycle⟩ := periodicComponent_has_periodic_representative (hperiodic C hC)
      obtain ⟨V, hV⟩ := fixed_basin_green_ratio_uniform_zero c hε
      refine ⟨V, ?_⟩
      intro v hv _ hvC
      apply hV v hv
      apply (shortcut_component_of_periodic_is_basin hcycle v).mp
      apply (shortcutTailLabel_eq_iff v c).mp
      exact hvC.trans hc.symm
    · exact ⟨0, fun _ _ hm _ => (hC hm).elim⟩
  choose V hV using hcuts
  refine ⟨s.sup V, ?_⟩
  intro v hv hnonperiodic
  by_cases hvs : shortcutTailLabel v ∈ s
  · have hle := Finset.le_sup (f := V) hvs
    exact hV (shortcutTailLabel v) v (by omega) hvs rfl
  · have htail : labelSubsetMass (s : Set ShortcutTailComponent)ᶜ actualShortcutTailLaw < ε / delta := by
      rw [labelSubsetMass_compl actualShortcutTailLaw_spec.1, labelSubsetMass_finset]
      linarith
    have hbasin := actualBasinDensity_le_labelSubsetMass v (s : Set ShortcutTailComponent)ᶜ hvs
    obtain ⟨_, _, hcompare⟩ := actual_basin_and_weighted_density_comparison
    have hD : actualFirstHitDensity v < ε / delta := ((hcompare v).1.trans hbasin).trans_lt htail
    have hpositive : 0 < v := by omega
    rw [green_density_ratio_of_nonperiodic hpositive hnonperiodic,
      abs_of_nonneg (mul_nonneg delta_pos.le (actualFirstHitDensity_nonneg v))]
    have h := (lt_div_iff₀ delta_pos).mp hD
    simpa only [mul_comm] using h

theorem nonperiodicGreenSublinear_iff_divergentComponentsNull :
    NonperiodicGreenSublinear ↔ DivergentComponentsNull :=
  ⟨divergent_components_null_of_sublinear, nonperiodic_green_sublinear_of_null⟩

theorem divergentComponentsNull_iff_divergentTraceVanishes :
    DivergentComponentsNull ↔ DivergentTraceVanishes :=
  ⟨divergent_trace_vanishes_of_null, divergent_components_null_of_trace_vanishes⟩

theorem forward_component_four_conditions_equivalent :
    List.TFAE [NonperiodicGreenSublinear, DivergentComponentsNull,
      EventuallyPeriodicDensityOne, DivergentTraceVanishes] := by
  tfae_have 1 ↔ 2 := nonperiodicGreenSublinear_iff_divergentComponentsNull
  tfae_have 2 ↔ 3 := divergentComponentsNull_iff_eventuallyPeriodicDensityOne
  tfae_have 2 ↔ 4 := divergentComponentsNull_iff_divergentTraceVanishes
  tfae_finish

theorem trace_vanishes_on_each_divergent_component (h : DivergentTraceVanishes)
    {n q : ℕ} (hinj : Function.Injective (fun i => iterate i n)) (hrel : ShortcutTailRelated q n) :
    actualDensityValue actualFirstHitDensity q = 0 :=
  h q (shortcut_component_injective hrel hinj)

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.nonperiodic_green_sublinear_of_null
#print axioms CollatzCanonical.ForwardComponent.forward_component_four_conditions_equivalent
