import MaskedEnergyBoundaryLimit
import SublinearNonperiodicCylinderEnergy

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao CollatzCanonical.ForwardComponent Erdos1135

noncomputable section

theorem nonperiodic_no_syracuse_return {N : ℕ} (hN : Odd N)
    (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r N = N)
    (j : ℕ) (hj : 0 < j) : (Tao.syracuse^[j]) N ≠ N := by
  intro hret
  apply hnp
  refine ⟨Tao.taoTupleWeight (Tao.syracuseValuationPNatList j N hN),
    hj.trans_le (le_syracuse_clock j N hN), ?_⟩
  simpa only [syracuse_shortcut_landing] using hret

theorem masked_canonicalRho_zero_of_multiple_three {K N : ℕ}
    (hK : 0 < K) (hN : Odd N) (hthree : N % 3 = 0)
    (hmask : ∀ j : ℕ, 0 < j → j ≤ K → (Tao.syracuse^[j]) N ≠ N) :
    canonicalRho K N = 0 := by
  obtain ⟨L, _, hbound⟩ := exists_uniform_odd_masked_cylinder_bound
  have h := hbound N hN K hK hmask
  rw [actual_weighted_density_zero_of_multiple_three hthree] at h
  linarith [canonicalRho_nonneg K N]

/-- The extra representative 3^K in the old inclusive head has zero mass. -/
theorem positiveOddNonperiodic_energy_le_masked_energy {K : ℕ} (hK : 0 < K) :
    positiveOddNonperiodicCylinderSquareEnergy K ≤ maskedCylinderHeadEnergy K := by
  let Q := (positiveOddNonperiodicCylinderHead K).filter (fun N => N < 3 ^ K)
  have hmem (N : ℕ) (hN : N ∈ positiveOddNonperiodicCylinderHead K) :
      0 < N ∧ N ≤ 3 ^ K ∧ Odd N ∧ ¬ ∃ r : ℕ, 0 < r ∧ iterate r N = N := by
    obtain ⟨hh, ho, hnp⟩ := Finset.mem_filter.mp hN
    have hh' := Finset.mem_Icc.mp hh
    exact ⟨by omega, hh'.2, ho, hnp⟩
  have he : positiveOddNonperiodicCylinderSquareEnergy K =
      ∑ N ∈ Q, (canonicalRho K N / (N : ℝ)) ^ 2 := by
    unfold positiveOddNonperiodicCylinderSquareEnergy
    dsimp only [Q]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro N hN
    by_cases hh : N < 3 ^ K
    · simp only [if_pos hh]
    · have hm := hmem N hN
      have heN : N = 3 ^ K := by omega
      have hthree : N % 3 = 0 := by
        rw [heN]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
        simp [pow_succ]
      have hz := masked_canonicalRho_zero_of_multiple_three hK hm.2.2.1 hthree
        (fun j hj _ => nonperiodic_no_syracuse_return hm.2.2.1 hm.2.2.2 j hj)
      simp only [if_neg hh, hz, zero_div, zero_pow (by decide : 2 ≠ 0)]
  have hsub : Q ⊆ maskedOddCylinderHead K := by
    intro N hN
    obtain ⟨hh, hheight⟩ := Finset.mem_filter.mp hN
    have hm := hmem N hh
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hheight, hm.2.2.1,
      fun j hj _ => nonperiodic_no_syracuse_return hm.2.2.1 hm.2.2.2 j hj⟩
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

theorem universal_eventual_periodicity_of_sublinear_masked_energy
    (henergy : Tendsto (fun K => maskedCylinderHeadEnergy K / ((K : ℝ) + 1))
      atTop (𝓝 0)) : UniversalEventualPeriodicity := by
  apply universal_eventual_periodicity_of_sublinear_odd_nonperiodic_energy
  apply squeeze_zero' ?_ ?_ henergy
  · exact Filter.Eventually.of_forall (fun K =>
      div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
    exact div_le_div_of_nonneg_right (positiveOddNonperiodic_energy_le_masked_energy hK)
      (by positivity)

#print axioms positiveOddNonperiodic_energy_le_masked_energy
#print axioms universal_eventual_periodicity_of_sublinear_masked_energy
end
end CollatzCanonical.PeriodicCensusFloor
