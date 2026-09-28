import ShortcutTailComponents

set_option autoImplicit false

namespace CollatzCanonical.ForwardComponent
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.LabelLaw CollatzCanonical.NativeTao Erdos1135.Tao

theorem shortcut_reaches_initial_oddPart (q : ℕ) :
    iterate (q.factorization 2) q = ordCompl[2] q := by
  have h := (even_run (q.factorization 2) (ordCompl[2] q)).1
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  exact h

theorem shortcut_reaches_standard_minimum {q : ℕ} (hq : 0 < q) :
    ∃ a : ℕ, iterate a q = collatzOrbitMin q := by
  obtain ⟨k, hk⟩ := syracuseGlobalMinimum_mem (ordCompl[2] q)
  let b := taoTupleWeight (syracuseValuationPNatList k (ordCompl[2] q) (ordCompl_two_odd hq))
  refine ⟨q.factorization 2 + b, ?_⟩
  rw [iterate_add, shortcut_reaches_initial_oddPart]
  change iterate (taoTupleWeight (syracuseValuationPNatList k (ordCompl[2] q)
    (ordCompl_two_odd hq))) (ordCompl[2] q) = collatzOrbitMin q
  rw [syracuse_shortcut_landing, hk, collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart hq]

theorem shortcut_component_spine_error_subset_minimum_tail (n M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ q : ℕ, 0 < q → ShortcutTailRelated q n →
      (¬ ∃ b, iterate b q = iterate j n) → M < collatzOrbitMin q := by
  obtain ⟨J, hJ⟩ := shortcut_component_not_in_spine_basin_large_minimum n M
  refine ⟨J, ?_⟩
  intro j hj q hq hrel hnot
  obtain ⟨a, ha⟩ := shortcut_reaches_standard_minimum hq
  rw [← ha]
  exact hJ j hj q hrel hnot a

end CollatzCanonical.ForwardComponent

#print axioms CollatzCanonical.ForwardComponent.shortcut_component_spine_error_subset_minimum_tail
