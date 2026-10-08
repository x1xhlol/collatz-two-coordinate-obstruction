import UnitSourceForwardDensity

/-!
# Uniform-unit source and finite density comparison

The actual uniform law on every unit residue modulo 3^(j+1), followed by
j geometric affine steps, equals the independently defined forward law.
Its finite L1 comparison with the native Syracuse law inherits every
polynomial rate from the frozen seed-uniform theorem. Both finite
counting-Haar and finite unit-Haar density normalizations are explicit.
No infinite Haar measure or canonical 3-adic measure identification is
asserted here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

/-- The two-point mixture represents every unit residue of the ambient seed,
not merely a substitute probability law: all higher seed digits cancel. -/
theorem unitSourceUniformSeed_bind_affine_eq_forward (j : ℕ) :
    (unitSourceUniformSeed j).bind (unitSourceAffinePMF (j + 1) j) =
      unitSourceForwardPMF j := by
  have hmap : (unitSourceUniformSeed j).bind (unitSourceAffinePMF (j + 1) j) =
      ((unitSourceUniformSeed j).map
        (taoZModThreeProjection (by omega : 1 ≤ j + 1))).bind
        (fun z => unitSourceAffinePMF (j + 1) j (z.val : ZMod (3 ^ (j + 1)))) := by
    rw [PMF.bind_map]
    apply congrArg (PMF.bind (unitSourceUniformSeed j))
    funext z
    exact unitSourceAffinePMF_seed_projection j z
  rw [hmap, unitSourceUniformSeed_projection_eq_initial,
    unitSourceInitialPMF, PMF.bind_map, unitSourceForwardPMF_eq_seed_mixture]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Fin 2)))
  funext b
  have hb : b.val + 1 < 3 := by omega
  change unitSourceAffinePMF (j + 1) j ((unitSourceUnitDigit b).val : ZMod (3 ^ (j + 1))) = _
  rw [unitSourceUnitDigit, ZMod.val_natCast_of_lt hb]

theorem unitSourceForwardPMF_apply_toReal
    (j : ℕ) (x : ZMod (3 ^ (j + 1))) :
    (unitSourceForwardPMF j x).toReal =
      ((unitSourceAffinePMF (j + 1) j 1 x).toReal +
        (unitSourceAffinePMF (j + 1) j 2 x).toReal) / 2 := by
  rw [unitSourceForwardPMF_eq_seed_mixture, unitSource_bind_apply_toReal_sum]
  simp only [Fin.sum_univ_two, PMF.uniformOfFintype_apply, Fintype.card_fin]
  norm_num
  ring

noncomputable def unitSourceForwardNativeL1Distance (j : ℕ) : ℝ :=
  ∑ x : ZMod (3 ^ (j + 1)),
    |(unitSourceForwardPMF j x).toReal - (syracPMF (j + 1) x).toReal|

theorem unitSourceForwardNativeL1Distance_le_seed_average (j : ℕ) :
    unitSourceForwardNativeL1Distance j ≤
      (unitSourceNativeL1Distance (j + 1) 1 +
        unitSourceNativeL1Distance (j + 1) 2) / 2 := by
  unfold unitSourceForwardNativeL1Distance unitSourceNativeL1Distance
  simp only [Nat.add_sub_cancel, unitSourceForwardPMF_apply_toReal]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro x _hx
  have h := abs_add_le
    ((unitSourceAffinePMF (j + 1) j 1 x).toReal - (syracPMF (j + 1) x).toReal)
    ((unitSourceAffinePMF (j + 1) j 2 x).toReal - (syracPMF (j + 1) x).toReal)
  calc
    _ = |((unitSourceAffinePMF (j + 1) j 1 x).toReal - (syracPMF (j + 1) x).toReal) +
        ((unitSourceAffinePMF (j + 1) j 2 x).toReal - (syracPMF (j + 1) x).toReal)| / 2 := by
      have htwo : (2 : ℝ) = |(2 : ℝ)| := by norm_num
      conv_rhs => rw [htwo, ← abs_div]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_right h (by norm_num)

theorem exists_unitSourceForwardNativeL1Distance_le_inv_pow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      unitSourceForwardNativeL1Distance j ≤ C / ((j + 1 : ℕ) : ℝ) ^ A := by
  obtain ⟨C, hC, h⟩ := exists_unitSourceNativeL1Distance_le_inv_pow A
  refine ⟨C, hC, fun j => ?_⟩
  have h1 := h (j + 1) (by omega) 1
  have h2 := h (j + 1) (by omega) 2
  have hmix := unitSourceForwardNativeL1Distance_le_seed_average j
  linarith

/-- The finite counting-Haar integral of the independent density error.
No infinite-space or canonical-measure identification is used here. -/
noncomputable def unitSourceFiniteDensityL1Error (j : ℕ) : ℝ :=
  (∑ x : ZMod (3 ^ (j + 1)),
    |(3 / 2 : ℝ) * unitSourceBranchDensity j x -
      (3 : ℝ) ^ (j + 1) * (syracPMF (j + 1) x).toReal|) / (3 : ℝ) ^ (j + 1)

theorem unitSourceFiniteDensityL1Error_eq_distance (j : ℕ) :
    unitSourceFiniteDensityL1Error j = unitSourceForwardNativeL1Distance j := by
  unfold unitSourceFiniteDensityL1Error unitSourceForwardNativeL1Distance
  simp_rw [← unitSourceForwardPMF_density_normalization, ← mul_sub,
    abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 3) (j + 1))]
  rw [← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 3) (j + 1)))

theorem exists_unitSourceFiniteDensityL1Error_le_inv_pow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      unitSourceFiniteDensityL1Error j ≤ C / ((j + 1 : ℕ) : ℝ) ^ A := by
  simpa only [unitSourceFiniteDensityL1Error_eq_distance] using
    exists_unitSourceForwardNativeL1Distance_le_inv_pow A

/-- Actual finite unit-Haar expectation of the unit-normalized density error. -/
noncomputable def unitSourceFiniteUnitDensityL1Error (j : ℕ) : ℝ :=
  ∑ x : ZMod (3 ^ (j + 1)), (unitSourceUniformSeed j x).toReal *
    |unitSourceBranchDensity j x -
      (2 / 3 : ℝ) * ((3 : ℝ) ^ (j + 1) * (syracPMF (j + 1) x).toReal)|

theorem unitSourceFiniteUnitDensityL1Error_le_distance (j : ℕ) :
    unitSourceFiniteUnitDensityL1Error j ≤ unitSourceForwardNativeL1Distance j := by
  unfold unitSourceFiniteUnitDensityL1Error unitSourceForwardNativeL1Distance
  apply Finset.sum_le_sum
  intro x _hx
  have hp : (0 : ℝ) < 2 * 3 ^ j := by positivity
  have hnorm : unitSourceBranchDensity j x -
      (2 / 3 : ℝ) * ((3 : ℝ) ^ (j + 1) * (syracPMF (j + 1) x).toReal) =
        (2 * (3 : ℝ) ^ j) *
          ((unitSourceForwardPMF j x).toReal - (syracPMF (j + 1) x).toReal) := by
    rw [unitSourceBranchDensity_eq_mass, pow_succ (3 : ℝ) j]
    ring
  rw [hnorm, abs_mul, abs_of_pos hp, unitSourceUniformSeed_apply_toReal]
  split_ifs
  · simpa only [zero_mul] using abs_nonneg
      ((unitSourceForwardPMF j x).toReal - (syracPMF (j + 1) x).toReal)
  · have hc : (1 / (2 * (3 : ℝ) ^ j)) * (2 * 3 ^ j) = 1 :=
      one_div_mul_cancel (ne_of_gt hp)
    rw [← mul_assoc, hc, one_mul]

theorem exists_unitSourceFiniteUnitDensityL1Error_le_inv_pow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      unitSourceFiniteUnitDensityL1Error j ≤ C / ((j + 1 : ℕ) : ℝ) ^ A := by
  obtain ⟨C, hC, h⟩ := exists_unitSourceForwardNativeL1Distance_le_inv_pow A
  exact ⟨C, hC, fun j => (unitSourceFiniteUnitDensityL1Error_le_distance j).trans (h j)⟩

#print axioms unitSourceUniformSeed_bind_affine_eq_forward
#print axioms exists_unitSourceFiniteDensityL1Error_le_inv_pow
#print axioms exists_unitSourceFiniteUnitDensityL1Error_le_inv_pow

end Erdos1135.Tao
