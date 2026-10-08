import TrapLaplaceEventBounds

/-! Exact event transport and comparisons restricted to positive PMF mass. -/

set_option autoImplicit false
open scoped BigOperators

namespace CollatzResearch

theorem trap_pmf_event_eq_outerMeasure {α : Type*} (p : PMF α) (E : α → Prop) :
    trapPMFEvent p E = (p.toOuterMeasure {a | E a}).toReal := by
  classical
  rw [← trap_pmf_event_toReal, PMF.toOuterMeasure_apply]
  congr 1
  unfold trapPMFEventENN
  apply tsum_congr
  intro a
  by_cases ha : E a <;> simp [ha]

theorem trap_pmf_event_map {α β : Type*} (p : PMF α) (f : α → β) (E : β → Prop) :
    trapPMFEvent (p.map f) E = trapPMFEvent p (fun a => E (f a)) := by
  rw [trap_pmf_event_eq_outerMeasure, trap_pmf_event_eq_outerMeasure,
    PMF.toOuterMeasure_map_apply]
  rfl

theorem trap_pmf_event_mono_on_support {α : Type*} (p : PMF α) (E F : α → Prop)
    (hEF : ∀ a, (p a).toReal ≠ 0 → E a → F a) :
    trapPMFEvent p E ≤ trapPMFEvent p F := by
  classical
  have hsum : ∀ G : α → Prop,
      Summable fun a => (p a).toReal * (if G a then (1 : ℝ) else 0) := by
    intro G
    apply trap_pmf_expectation_summable
    · intro a; split_ifs <;> norm_num
    · intro a; split_ifs <;> norm_num
  unfold trapPMFEvent trapPMFExpectation
  apply (hsum E).tsum_le_tsum _ (hsum F)
  intro a
  by_cases hp : (p a).toReal = 0
  · simp [hp]
  by_cases he : E a
  · simp [he, hEF a hp he]
  · simp only [he, ite_false, mul_zero]
    split_ifs <;> positivity

theorem trap_pmf_event_congr_on_support {α : Type*} (p : PMF α) (E F : α → Prop)
    (hEF : ∀ a, (p a).toReal ≠ 0 → (E a ↔ F a)) :
    trapPMFEvent p E = trapPMFEvent p F := by
  apply le_antisymm
  · exact trap_pmf_event_mono_on_support p E F (fun a ha => (hEF a ha).mp)
  · exact trap_pmf_event_mono_on_support p F E (fun a ha => (hEF a ha).mpr)

end CollatzResearch

#print axioms CollatzResearch.trap_pmf_event_map
#print axioms CollatzResearch.trap_pmf_event_mono_on_support
