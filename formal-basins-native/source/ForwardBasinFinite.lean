import HittingTimeClassification

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- One forward orbit meets a fixed backward basin in finitely many values. -/
theorem forward_orbit_inter_basin_finite (q N : ℕ) :
    {v : ℕ | (∃ j, iterate j q = v) ∧ ∃ k, iterate k v = N}.Finite := by
  classical
  by_cases hhit : ∃ K, iterate K q = N
  · obtain ⟨K, hK⟩ := hhit
    by_cases hperiod : ∃ p, 0 < p ∧ iterate p N = N
    · obtain ⟨p, hp, hret⟩ := hperiod
      apply ((Finset.range K).image (fun j => iterate j q) ∪
        (Finset.range p).image (fun j => iterate j N)).finite_toSet.subset
      rintro v ⟨⟨j, rfl⟩, _⟩
      by_cases hj : j < K
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(j - K) % p, Finset.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
        have he : iterate j q = iterate (j - K) N := by
          rw [← hK, ← iterate_add, Nat.add_sub_of_le (Nat.le_of_not_gt hj)]
        exact (iterate_eq_mod_period hret (j - K)).symm.trans he.symm
    · have hno : ∀ p, 0 < p → iterate p N ≠ N := by
        intro p hp hr
        exact hperiod ⟨p, hp, hr⟩
      let hf := firstHitTime_spec (show ∃ K, iterate K q = N from ⟨K, hK⟩)
      apply ((Finset.range (firstHitTime ⟨K, hK⟩ + 1)).image
        (fun j => iterate j q)).finite_toSet.subset
      rintro v ⟨⟨j, rfl⟩, ⟨k, hk⟩⟩
      have he : iterate (j + k) q = N := by rw [iterate_add]; exact hk
      have hjk := (hitting_time_iff_eq_first_of_no_return hf hno).mp he
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  · have hempty : {v : ℕ | (∃ j, iterate j q = v) ∧ ∃ k, iterate k v = N} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
      exact hhit ⟨j + k, by rw [iterate_add, hj, hk]⟩
    rw [hempty]
    exact Set.finite_empty

/-- Only finitely many targets in a fixed basin have a bounded ancestor. -/
theorem bounded_ancestor_targets_in_basin_finite (M N : ℕ) :
    {v : ℕ | (∃ k, iterate k v = N) ∧
      ∃ q ≤ M, ∃ j, iterate j q = v}.Finite := by
  have hu : (⋃ q ∈ (Finset.range (M + 1) : Set ℕ),
      {v : ℕ | (∃ j, iterate j q = v) ∧ ∃ k, iterate k v = N}).Finite := by
    apply (Finset.range (M + 1)).finite_toSet.biUnion
    intro q _
    exact forward_orbit_inter_basin_finite q N
  apply hu.subset
  rintro v ⟨hv, q, hq, hj⟩
  exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (by omega), hj, hv⟩⟩

/-- Above a finite cutoff, targets in one fixed basin have no bounded ancestor. -/
theorem eventually_basin_targets_have_no_small_ancestor (M N : ℕ) :
    ∃ V : ℕ, ∀ v : ℕ, V < v → (∃ k, iterate k v = N) →
      ∀ q : ℕ, q ≤ M → ¬ ∃ j, iterate j q = v := by
  classical
  let s := (bounded_ancestor_targets_in_basin_finite M N).toFinset
  refine ⟨s.sup id, ?_⟩
  intro v hv htarget q hq hhit
  have hmem : v ∈ s := by
    exact (bounded_ancestor_targets_in_basin_finite M N).mem_toFinset.mpr
      ⟨htarget, q, hq, hhit⟩
  have hle : v ≤ s.sup id := Finset.le_sup (f := id) hmem
  omega

#print axioms forward_orbit_inter_basin_finite
#print axioms bounded_ancestor_targets_in_basin_finite
#print axioms eventually_basin_targets_have_no_small_ancestor

end CollatzCylinderPacking.Arithmetic

namespace CollatzCylinderPacking.Arithmetic

/-- A periodic ancestor returns from every value it reaches. -/
theorem periodic_ancestor_reaches_back {v N : ℕ}
    (hperiod : ∃ p, 0 < p ∧ iterate p v = v)
    (hhit : ∃ K, iterate K v = N) : ∃ K, iterate K N = v := by
  obtain ⟨p, hp, hret⟩ := hperiod
  obtain ⟨K, hK⟩ := hhit
  have hle : K ≤ (K + 1) * p := by nlinarith
  refine ⟨(K + 1) * p - K, ?_⟩
  rw [← hK, ← iterate_add, Nat.add_sub_of_le hle]
  exact iterate_mul_period hret (K + 1)

/-- A fixed backward basin contains only finitely many periodic targets. -/
theorem periodic_targets_in_basin_finite (N : ℕ) :
    {v : ℕ | (∃ K, iterate K v = N) ∧ ∃ p, 0 < p ∧ iterate p v = v}.Finite := by
  apply (forward_orbit_inter_basin_finite N N).subset
  rintro v ⟨hhit, hperiod⟩
  exact ⟨periodic_ancestor_reaches_back hperiod hhit, hhit⟩

theorem eventually_basin_targets_nonperiodic (N : ℕ) :
    ∃ V : ℕ, ∀ v : ℕ, V < v → (∃ K, iterate K v = N) →
      ¬ ∃ p, 0 < p ∧ iterate p v = v := by
  classical
  let s := (periodic_targets_in_basin_finite N).toFinset
  refine ⟨s.sup id, ?_⟩
  intro v hv hhit hperiod
  have hmem : v ∈ s :=
    (periodic_targets_in_basin_finite N).mem_toFinset.mpr ⟨hhit, hperiod⟩
  have hle : v ≤ s.sup id := Finset.le_sup (f := id) hmem
  omega

#print axioms periodic_targets_in_basin_finite
#print axioms eventually_basin_targets_nonperiodic

end CollatzCylinderPacking.Arithmetic
