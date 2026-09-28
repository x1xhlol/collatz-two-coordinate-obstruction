import StandardCollatzGlobalMinimum
import NativeTaoArithmeticBridge
import Mathlib.Order.Filter.Cofinite

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.LabelLaw CollatzCanonical.NativeTao

def ShortcutTailRelated (q n : ℕ) : Prop :=
  ∃ i j : ℕ, iterate i q = iterate j n

theorem shortcut_iterate_comm (a b q : ℕ) :
    iterate a (iterate b q) = iterate b (iterate a q) := by
  rw [← iterate_add, ← iterate_add, Nat.add_comm]

theorem ShortcutTailRelated_equivalence : Equivalence ShortcutTailRelated := by
  constructor
  · intro q
    exact ⟨0, 0, rfl⟩
  · rintro q n ⟨i, j, hij⟩
    exact ⟨j, i, hij.symm⟩
  · rintro q n r ⟨i, j, hij⟩ ⟨k, l, hkl⟩
    refine ⟨i + k, l + j, ?_⟩
    rw [iterate_add, iterate_add, hij, shortcut_iterate_comm, hkl]

def shortcutTailSetoid : Setoid ℕ := ⟨ShortcutTailRelated, ShortcutTailRelated_equivalence⟩
abbrev ShortcutTailComponent := Quotient shortcutTailSetoid

def shortcutTailLabel (q : ℕ) : ShortcutTailComponent := Quotient.mk shortcutTailSetoid q

theorem shortcutTailLabel_eq_iff (q n : ℕ) :
    shortcutTailLabel q = shortcutTailLabel n ↔ ShortcutTailRelated q n := Quotient.eq

theorem shortcut_tail_related_iterate (n j : ℕ) : ShortcutTailRelated n (iterate j n) :=
  ⟨j, 0, rfl⟩

theorem shortcutTailLabel_iterate (n j : ℕ) :
    shortcutTailLabel (iterate j n) = shortcutTailLabel n := by
  apply Quotient.sound
  exact ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate n j)

theorem shortcut_tail_label_passage_invariant :
    EventuallyLabelPassageInvariant shortcutTailLabel := by
  apply Filter.Eventually.of_forall
  intro x q hq τ _
  rw [← syracuse_shortcut_landing τ q hq]
  exact (shortcutTailLabel_iterate q _).symm

theorem shortcutTailLabel_halving (q : ℕ) :
    shortcutTailLabel (2 * q) = shortcutTailLabel q := by
  apply Quotient.sound
  refine ⟨1, 0, ?_⟩
  change step (2 * q) = q
  simp [step]

theorem shortcut_basin_spine_monotone {q n i j : ℕ} (hij : i ≤ j)
    (hq : ∃ a, iterate a q = iterate i n) : ∃ a, iterate a q = iterate j n := by
  obtain ⟨a, ha⟩ := hq
  refine ⟨a + (j - i), ?_⟩
  rw [iterate_add, ha, ← iterate_add, Nat.add_sub_of_le hij]

theorem shortcut_component_iff_exists_spine_basin (q n : ℕ) :
    ShortcutTailRelated q n ↔ ∃ j a, iterate a q = iterate j n := by
  constructor <;> rintro ⟨a, j, h⟩ <;> exact ⟨j, a, h⟩

theorem shortcut_component_eventually_spine_basin {q n : ℕ} (hq : ShortcutTailRelated q n) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ a, iterate a q = iterate j n := by
  obtain ⟨a, J, h⟩ := hq
  exact ⟨J, fun j hj => shortcut_basin_spine_monotone hj ⟨a, h⟩⟩

theorem shortcut_component_finite_cutoff_capture (n M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ u : ℕ, u ≤ M → ShortcutTailRelated u n →
      ∃ a, iterate a u = iterate j n := by
  classical
  have hp : ∀ u : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ShortcutTailRelated u n →
      ∃ a, iterate a u = iterate j n := by
    intro u
    by_cases hu : ShortcutTailRelated u n
    · obtain ⟨J, hJ⟩ := shortcut_component_eventually_spine_basin hu
      exact ⟨J, fun j hj _ => hJ j hj⟩
    · exact ⟨0, fun _ _ h => (hu h).elim⟩
  choose J hJ using hp
  refine ⟨(Finset.range (M + 1)).sup J, ?_⟩
  intro j hj u hu hrel
  exact hJ u j ((Finset.le_sup (f := J) (Finset.mem_range.mpr (by omega))).trans hj) hrel

theorem shortcut_component_small_visit_capture (n M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ q : ℕ, ShortcutTailRelated q n →
      (∃ a, iterate a q ≤ M) → ∃ b, iterate b q = iterate j n := by
  obtain ⟨J, hJ⟩ := shortcut_component_finite_cutoff_capture n M
  refine ⟨J, ?_⟩
  intro j hj q hq ⟨a, ha⟩
  have hrel : ShortcutTailRelated (iterate a q) n :=
    ShortcutTailRelated_equivalence.trans
      (ShortcutTailRelated_equivalence.symm (shortcut_tail_related_iterate q a)) hq
  obtain ⟨b, hb⟩ := hJ j hj (iterate a q) ha hrel
  exact ⟨a + b, by rw [iterate_add, hb]⟩

theorem shortcut_component_not_in_spine_basin_large_minimum (n M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ q : ℕ, ShortcutTailRelated q n →
      (¬ ∃ b, iterate b q = iterate j n) → ∀ a : ℕ, M < iterate a q := by
  obtain ⟨J, hJ⟩ := shortcut_component_small_visit_capture n M
  refine ⟨J, ?_⟩
  intro j hj q hq hnot a
  by_contra h
  exact hnot (hJ j hj q hq ⟨a, by omega⟩)

theorem shortcut_component_injective {q n : ℕ} (hrel : ShortcutTailRelated q n)
    (hn : Function.Injective (fun j => iterate j n)) :
    Function.Injective (fun j => iterate j q) := by
  obtain ⟨i, j, hij⟩ := hrel
  intro a b hab
  change iterate a q = iterate b q at hab
  have he : iterate (j + a) n = iterate (j + b) n := by
    rw [iterate_add, iterate_add, ← hij, shortcut_iterate_comm a i q,
      shortcut_iterate_comm b i q, hab]
  have h := hn he
  omega

theorem shortcut_divergent_spine_tendsto_atTop {n : ℕ}
    (hn : Function.Injective (fun j => iterate j n)) :
    Tendsto (fun j => iterate j n) atTop atTop := hn.nat_tendsto_atTop

theorem shortcut_component_target_nonperiodic {q n : ℕ} (hrel : ShortcutTailRelated q n)
    (hn : Function.Injective (fun j => iterate j n)) :
    ∀ r : ℕ, 0 < r → iterate r q ≠ q := by
  intro r hr he
  have h := shortcut_component_injective hrel hn (show iterate r q = iterate 0 q from he)
  omega

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.shortcut_component_small_visit_capture
#print axioms CollatzCanonical.ForwardComponent.shortcut_component_injective
#print axioms CollatzCanonical.ForwardComponent.shortcut_tail_label_passage_invariant
