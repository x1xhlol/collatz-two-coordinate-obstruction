import CountableLabelLawCorollaries

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw

theorem labelSubsetMass_nat_tail_eq (p : LabelVector ℕ) (M : ℕ) :
    labelSubsetMass {i | M < i} p = ∑' k : ℕ, p (k + (M + 1)) := by
  classical
  let f : ℕ → ℝ := {i | M < i}.indicator (fun i => p i)
  have hf : Summable f := (lp.memℓp p).summable_of_one.indicator {i | M < i}
  have he := hf.sum_add_tsum_nat_add (M + 1)
  have hzero : ∑ i ∈ Finset.range (M + 1), f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiM : i ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq, if_neg (not_lt.mpr hiM)]
  rw [hzero, zero_add] at he
  change (∑' i, f i) = _
  rw [← he]
  apply tsum_congr
  intro k
  simp only [f, Set.indicator_apply, Set.mem_setOf_eq, if_pos (by omega : M < k + (M + 1))]

theorem probability_vector_nat_tail_tendsto_zero (p : LabelVector ℕ) :
    Tendsto (fun M : ℕ => labelSubsetMass {i | M < i} p) atTop (𝓝 0) := by
  simp_rw [labelSubsetMass_nat_tail_eq]
  exact (tendsto_sum_nat_add (fun i => p i)).comp (tendsto_add_atTop_nat 1)

theorem actual_minimum_label_tightness :
    ∃ p : LabelVector ℕ, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw syracuseGlobalMinimum) atTop (𝓝 p) ∧
      Tendsto (fullLabelLaw (oddPartLabel syracuseGlobalMinimum)) atTop (𝓝 p) ∧
      Tendsto (fun M : ℕ => labelSubsetMass {i | M < i} p) atTop (𝓝 0) := by
  obtain ⟨p, hp, ho, hf⟩ := actual_odd_and_all_start_label_law _
    global_minimum_eventually_passage_invariant
  exact ⟨p, hp, ho, hf, probability_vector_nat_tail_tendsto_zero p⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.probability_vector_nat_tail_tendsto_zero
#print axioms CollatzCanonical.LabelLaw.actual_minimum_label_tightness
