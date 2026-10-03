import MaskedEnergySufficiency

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.ForwardComponent

noncomputable section

theorem forward_orbit_finite_of_eventually_periodic {q : ℕ}
    (hq : ∃ c : ℕ, (∃ A, iterate A q = c) ∧
      ∃ p : ℕ, 0 < p ∧ iterate p c = c) :
    {v : ℕ | ∃ j, iterate j q = v}.Finite := by
  obtain ⟨c, ⟨A, hA⟩, p, hp, hret⟩ := hq
  apply ((Finset.range A).image (fun j => iterate j q) ∪
    (Finset.range p).image (fun j => iterate j c)).finite_toSet.subset
  rintro v ⟨j, rfl⟩
  by_cases hj : j < A
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(j - A) % p, Finset.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
    have he : iterate j q = iterate (j - A) c := by
      rw [← hA, ← iterate_add, Nat.add_sub_of_le (Nat.le_of_not_gt hj)]
    exact (iterate_eq_mod_period hret (j - A)).symm.trans he.symm

/-- Under eventual periodicity, every fixed collection of bounded seeds
has only finitely many forward target values, including its cycle values. -/
theorem small_ancestor_targets_finite_of_universal_eventual_periodicity
    (huep : UniversalEventualPeriodicity) (M : ℝ) :
    {N : ℕ | ¬ NoSmallAncestor N M}.Finite := by
  have hu : (⋃ q ∈ (Finset.Icc 1 (Nat.floor M) : Set ℕ),
      {N : ℕ | ∃ j, iterate j q = N}).Finite := by
    apply (Finset.Icc 1 (Nat.floor M)).finite_toSet.biUnion
    intro q hq
    exact forward_orbit_finite_of_eventually_periodic
      (huep q (Finset.mem_Icc.mp hq).1)
  apply hu.subset
  intro N hN
  simp only [Set.mem_setOf_eq, NoSmallAncestor] at hN
  push Not at hN
  obtain ⟨q, hq, hqM, j, hj⟩ := hN
  exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
    ⟨Finset.mem_Icc.mpr ⟨hq, Nat.le_floor hqM⟩, j, hj⟩⟩

theorem fixed_small_ancestor_energy_bounded_of_universal_eventual_periodicity
    (huep : UniversalEventualPeriodicity) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 0 < K →
      maskedSmallAncestorEnergy K M ≤ C := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_odd_masked_cylinder_bound
  obtain ⟨P, _, hcompare⟩ := actual_basin_and_weighted_density_comparison
  let F := (small_ancestor_targets_finite_of_universal_eventual_periodicity huep M).toFinset
  refine ⟨(F.card : ℝ) * L ^ 2, by positivity, ?_⟩
  intro K hK
  let Q := (maskedOddCylinderHead K).filter (fun N => ¬ NoSmallAncestor N M)
  have hsub : Q ⊆ F := by
    intro N hN
    exact (small_ancestor_targets_finite_of_universal_eventual_periodicity huep M).mem_toFinset.mpr
      (Finset.mem_filter.mp hN).2
  have hamp (N : ℕ) (hN : N ∈ Q) : (canonicalRho K N / (N : ℝ)) ^ 2 ≤ L ^ 2 := by
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hN
    obtain ⟨_, hodd, hmask⟩ := Finset.mem_filter.mp hm
    have hp : (0 : ℝ) < N := by exact_mod_cast hodd.pos
    have h := hbound N hodd K hK hmask
    have hD : actualFirstHitDensity N ≤ 1 :=
      (hcompare N).1.trans (actualBasinDensity_bounds N).2
    have hn : canonicalRho K N / (N : ℝ) ≤ L := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_le_mul_of_nonneg_left hD (mul_nonneg hL.le hp.le)]
    exact (sq_le_sq₀ (div_nonneg (canonicalRho_nonneg _ _) hp.le) hL.le).mpr hn
  change (∑ N ∈ Q, (canonicalRho K N / (N : ℝ)) ^ 2) ≤ _
  calc
    _ ≤ ∑ _N ∈ Q, L ^ 2 := Finset.sum_le_sum hamp
    _ ≤ ∑ _N ∈ F, L ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = _ := by simp

theorem masked_energy_sublinear_of_universal_eventual_periodicity
    (huep : UniversalEventualPeriodicity) :
    Tendsto (fun K => maskedCylinderHeadEnergy K / ((K : ℝ) + 1)) atTop (𝓝 0) := by
  obtain ⟨L, hL, ε, hε, hεlim, _, hbound⟩ := exists_uniform_maskedEnergy_decomposition
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun K => ha.trans_le
      (div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)))
  · intro b hb
    obtain ⟨M, hM⟩ := (hεlim.eventually_lt_const (by positivity : 0 < b / (10 * L))).exists
    obtain ⟨C, hC, hfixed⟩ :=
      fixed_small_ancestor_energy_bounded_of_universal_eventual_periodicity huep M
    have hlimC : Tendsto (fun K : ℕ => C / ((K : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
    filter_upwards [hlimC.eventually_lt_const (half_pos hb), eventually_gt_atTop (0 : ℕ)]
      with K hCK hK
    have htotal := (hbound K hK M).2
    have hsmall := hfixed K hK
    have hbudget := mul_le_mul_of_nonneg_left (cylinderHeadL1Budget_le_linear K)
      (mul_nonneg hL.le (hε M))
    have heps : 5 * L * ε M < b / 2 := by
      have := (lt_div_iff₀ (by positivity : 0 < 10 * L)).mp hM
      nlinarith
    have hnorm : maskedCylinderHeadEnergy K / ((K : ℝ) + 1) ≤
        C / ((K : ℝ) + 1) + 5 * L * ε M := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) + 1)).mpr
      have he : C / ((K : ℝ) + 1) * ((K : ℝ) + 1) = C :=
        div_mul_cancel₀ _ (by positivity)
      nlinarith
    linarith

/-- A finite numerical head and finite return mask give an exact criterion;
neither side is asserted without the other as a hypothesis. -/
theorem masked_energy_sublinear_iff_universal_eventual_periodicity :
    Tendsto (fun K => maskedCylinderHeadEnergy K / ((K : ℝ) + 1)) atTop (𝓝 0) ↔
      UniversalEventualPeriodicity :=
  ⟨universal_eventual_periodicity_of_sublinear_masked_energy,
    masked_energy_sublinear_of_universal_eventual_periodicity⟩

theorem small_ancestor_energy_sublinear_iff_universal_eventual_periodicity
    (M : ℕ → ℝ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun K => maskedSmallAncestorEnergy K (M K) / ((K : ℝ) + 1))
      atTop (𝓝 0) ↔ UniversalEventualPeriodicity :=
  (masked_energy_sublinear_iff_smallAncestor_energy_sublinear M hM).symm.trans
    masked_energy_sublinear_iff_universal_eventual_periodicity

#print axioms forward_orbit_finite_of_eventually_periodic
#print axioms small_ancestor_targets_finite_of_universal_eventual_periodicity
#print axioms fixed_small_ancestor_energy_bounded_of_universal_eventual_periodicity
#print axioms masked_energy_sublinear_of_universal_eventual_periodicity
#print axioms masked_energy_sublinear_iff_universal_eventual_periodicity
#print axioms small_ancestor_energy_sublinear_iff_universal_eventual_periodicity
end
end CollatzCanonical.PeriodicCensusFloor
