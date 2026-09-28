import StandardCollatzGlobalMinimum

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open Erdos1135 Erdos1135.Tao

theorem collatzOrbitMin_halving {q : ℕ} (hq : 0 < q) :
    collatzOrbitMin (2 * q) = collatzOrbitMin q := by
  rw [collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart (by omega : 0 < 2 * q),
    collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart hq]
  congr 1
  simpa only [pow_one] using Nat.ordCompl_self_pow_mul q 1 Nat.prime_two

theorem standard_global_minimum_eventually_passage_invariant :
    EventuallyLabelPassageInvariant collatzOrbitMin := by
  apply Filter.Eventually.of_forall
  intro x q hq τ hτ
  rw [collatzOrbitMin_eq_syracuseGlobalMinimum_of_odd hq,
    collatzOrbitMin_eq_syracuseGlobalMinimum_of_odd (syracuse_iterate_odd_trajectory τ q hq)]
  exact syracuseGlobalMinimum_first_passage hτ

theorem actual_standard_global_minimum_label_law :
    ∃ μ : PMF ℕ, Tendsto
      (fun t => ∑' i, |oddLabelLaw collatzOrbitMin t i - (μ i).toReal|)
      atTop (𝓝 0) :=
  actual_odd_label_PMF_law collatzOrbitMin standard_global_minimum_eventually_passage_invariant

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.collatzOrbitMin_halving
#print axioms CollatzCanonical.LabelLaw.standard_global_minimum_eventually_passage_invariant
#print axioms CollatzCanonical.LabelLaw.actual_standard_global_minimum_label_law
