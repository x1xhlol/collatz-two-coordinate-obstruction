import ShortcutTailComponents
import ForwardBasinFinite

set_option autoImplicit false

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

def periodicComponents : Set ShortcutTailComponent :=
  {C | ∃ q : ℕ, shortcutTailLabel q = C ∧ ¬ Function.Injective (fun j => iterate j q)}

theorem shortcut_noninjective_iff_hits_periodic (q : ℕ) :
    (¬ Function.Injective (fun j => iterate j q)) ↔
      ∃ c : ℕ, (∃ A, iterate A q = c) ∧ ∃ r, 0 < r ∧ iterate r c = c := by
  constructor
  · intro h
    have hex : ∃ a b : ℕ, a < b ∧ iterate a q = iterate b q := by
      simp only [Function.Injective, not_forall] at h
      obtain ⟨a, b, he, hne⟩ := h
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact ⟨a, b, hab, he⟩
      · exact ⟨b, a, hba, he.symm⟩
    obtain ⟨a, b, hab, he⟩ := hex
    refine ⟨iterate a q, ⟨a, rfl⟩, b - a, by omega, ?_⟩
    rw [← iterate_add, Nat.add_sub_of_le hab.le]
    exact he.symm
  · rintro ⟨c, ⟨A, hA⟩, r, hr, hret⟩ hinj
    have he : iterate (A + r) q = iterate A q := by rw [iterate_add, hA, hret]
    have h := hinj he
    omega

theorem mem_periodicComponents_iff (q : ℕ) :
    shortcutTailLabel q ∈ periodicComponents ↔ ¬ Function.Injective (fun j => iterate j q) := by
  constructor
  · rintro ⟨n, hn, hnon⟩ hq
    have hrel := (shortcutTailLabel_eq_iff n q).mp hn
    exact hnon (shortcut_component_injective hrel hq)
  · intro hq
    exact ⟨q, rfl, hq⟩

theorem shortcut_component_of_periodic_is_basin {N : ℕ}
    (hN : ∃ r, 0 < r ∧ iterate r N = N) (q : ℕ) :
    ShortcutTailRelated q N ↔ ∃ A, iterate A q = N := by
  constructor
  · rintro ⟨i, j, hij⟩
    obtain ⟨k, hk⟩ := periodic_ancestor_reaches_back hN (show ∃ K, iterate K N = iterate j N from ⟨j, rfl⟩)
    exact ⟨i + k, by rw [iterate_add, hij, hk]⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, 0, hA⟩

theorem periodicComponent_has_periodic_representative {C : ShortcutTailComponent}
    (hC : C ∈ periodicComponents) :
    ∃ c : ℕ, shortcutTailLabel c = C ∧ ∃ r, 0 < r ∧ iterate r c = c := by
  obtain ⟨q, hq, hnon⟩ := hC
  obtain ⟨c, ⟨A, hA⟩, hperiod⟩ := (shortcut_noninjective_iff_hits_periodic q).mp hnon
  refine ⟨c, ?_, hperiod⟩
  rw [← hA, shortcutTailLabel_iterate, hq]

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.shortcut_noninjective_iff_hits_periodic
#print axioms CollatzCanonical.ForwardComponent.shortcut_component_of_periodic_is_basin
