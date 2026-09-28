import ForwardComponentEquivalences
import ActualUnitSupport

set_option autoImplicit false

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem actual_component_mass_positive {n : ℕ} (hn : 0 < n) :
    0 < actualComponentMass n := by
  obtain ⟨k, hkpos, hkunit⟩ := positive_target_reaches_unit hn
  rw [actualComponentMass_eq_of_related (shortcut_tail_related_iterate n k)]
  exact (actual_basin_density_pos_of_unit hkpos hkunit).trans_le
    (actualBasinDensity_le_component_mass (iterate k n))

theorem actual_component_probability_positive {n : ℕ} (hn : 0 < n) :
    0 < (actualShortcutTailPMF (shortcutTailLabel n)).toReal := by
  rw [← actualComponentMass_eq_PMF]
  exact actual_component_mass_positive hn

def UniversalEventualPeriodicity : Prop :=
  ∀ n : ℕ, 0 < n → ∃ c : ℕ, (∃ A, iterate A n = c) ∧
    ∃ r : ℕ, 0 < r ∧ iterate r c = c

theorem divergentComponentsNull_iff_universalEventualPeriodicity :
    DivergentComponentsNull ↔ UniversalEventualPeriodicity := by
  constructor
  · intro hnull n hn
    apply (shortcut_noninjective_iff_hits_periodic n).mp
    intro hinj
    have hp := actual_component_mass_positive hn
    rw [hnull n hinj] at hp
    exact (lt_irrefl 0) hp
  · intro hperiodic n hinj
    exact ((shortcut_noninjective_iff_hits_periodic n).mpr
      (hperiodic n (shortcut_injective_start_positive hinj)) hinj).elim

theorem nonperiodicGreenSublinear_iff_universalEventualPeriodicity :
    NonperiodicGreenSublinear ↔ UniversalEventualPeriodicity :=
  nonperiodicGreenSublinear_iff_divergentComponentsNull.trans
    divergentComponentsNull_iff_universalEventualPeriodicity

theorem eventuallyPeriodicDensityOne_iff_universalEventualPeriodicity :
    EventuallyPeriodicDensityOne ↔ UniversalEventualPeriodicity :=
  divergentComponentsNull_iff_eventuallyPeriodicDensityOne.symm.trans
    divergentComponentsNull_iff_universalEventualPeriodicity

theorem divergentTraceVanishes_iff_universalEventualPeriodicity :
    DivergentTraceVanishes ↔ UniversalEventualPeriodicity :=
  divergentComponentsNull_iff_divergentTraceVanishes.symm.trans
    divergentComponentsNull_iff_universalEventualPeriodicity

theorem forward_component_five_conditions_equivalent :
    List.TFAE [NonperiodicGreenSublinear, DivergentComponentsNull,
      EventuallyPeriodicDensityOne, DivergentTraceVanishes, UniversalEventualPeriodicity] := by
  tfae_have 1 ↔ 2 := nonperiodicGreenSublinear_iff_divergentComponentsNull
  tfae_have 2 ↔ 3 := divergentComponentsNull_iff_eventuallyPeriodicDensityOne
  tfae_have 2 ↔ 4 := divergentComponentsNull_iff_divergentTraceVanishes
  tfae_have 2 ↔ 5 := divergentComponentsNull_iff_universalEventualPeriodicity
  tfae_finish

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.actual_component_mass_positive
#print axioms CollatzCanonical.ForwardComponent.actual_component_probability_positive
#print axioms CollatzCanonical.ForwardComponent.divergentComponentsNull_iff_universalEventualPeriodicity
#print axioms CollatzCanonical.ForwardComponent.nonperiodicGreenSublinear_iff_universalEventualPeriodicity
#print axioms CollatzCanonical.ForwardComponent.eventuallyPeriodicDensityOne_iff_universalEventualPeriodicity
#print axioms CollatzCanonical.ForwardComponent.divergentTraceVanishes_iff_universalEventualPeriodicity
#print axioms CollatzCanonical.ForwardComponent.forward_component_five_conditions_equivalent
