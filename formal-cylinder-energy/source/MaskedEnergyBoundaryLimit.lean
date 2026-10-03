import MaskedCylinderNoSmallAncestorEnergy

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

theorem cylinderHeadL1Budget_le_linear (K : ℕ) :
    cylinderHeadL1Budget K ≤ 5 * ((K : ℝ) + 1) := by
  have hp : (64 / 81 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ht := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 + 2 * (K : ℝ))
  unfold cylinderHeadL1Budget
  nlinarith

theorem maskedNoSmallAncestorEnergy_nonneg (K : ℕ) (M : ℝ) :
    0 ≤ maskedNoSmallAncestorEnergy K M :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem maskedSmallAncestorEnergy_nonneg (K : ℕ) (M : ℝ) :
    0 ≤ maskedSmallAncestorEnergy K M :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Any barrier tending to infinity removes the normalized no-small-ancestor
energy. There is no restriction on how slowly or quickly the barrier grows. -/
theorem moving_barrier_noSmallAncestor_energy_tendsto_zero
    (M : ℕ → ℝ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun K => maskedNoSmallAncestorEnergy K (M K) / ((K : ℝ) + 1))
      atTop (𝓝 0) := by
  obtain ⟨L, hL, ε, hε, hεlim, _, hbound⟩ := exists_uniform_maskedEnergy_decomposition
  have hdom : Tendsto (fun K => (5 * L) * ε (M K)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hεlim.comp hM).const_mul (5 * L)
  apply squeeze_zero' ?_ ?_ hdom
  · exact Filter.Eventually.of_forall (fun K =>
      div_nonneg (maskedNoSmallAncestorEnergy_nonneg K (M K)) (by positivity))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
    have hb := (hbound K hK (M K)).1
    have hl := mul_le_mul_of_nonneg_left (cylinderHeadL1Budget_le_linear K)
      (mul_nonneg hL.le (hε (M K)))
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) + 1)).mpr
    nlinarith only [hb, hl]

/-- The normalized total energy vanishes exactly when the remaining energy
on forward orbits of small seeds does, for any diverging choice of barrier. -/
theorem masked_energy_sublinear_iff_smallAncestor_energy_sublinear
    (M : ℕ → ℝ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun K => maskedCylinderHeadEnergy K / ((K : ℝ) + 1)) atTop (𝓝 0) ↔
      Tendsto (fun K => maskedSmallAncestorEnergy K (M K) / ((K : ℝ) + 1))
        atTop (𝓝 0) := by
  have hno := moving_barrier_noSmallAncestor_energy_tendsto_zero M hM
  constructor
  · intro htotal
    have hh := htotal.sub hno
    simp only [sub_zero] at hh
    apply hh.congr
    intro K
    rw [← sub_div, maskedCylinderHeadEnergy_split K (M K)]
    congr 1
    ring
  · intro hsmall
    have hh := hno.add hsmall
    simp only [add_zero] at hh
    apply hh.congr
    intro K
    rw [← add_div, ← maskedCylinderHeadEnergy_split K (M K)]

#print axioms cylinderHeadL1Budget_le_linear
#print axioms moving_barrier_noSmallAncestor_energy_tendsto_zero
#print axioms masked_energy_sublinear_iff_smallAncestor_energy_sublinear

end CollatzCanonical.PeriodicCensusFloor
