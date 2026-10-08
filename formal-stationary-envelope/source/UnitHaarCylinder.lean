import PadicHaarCylinder

/-!
# Unit Haar projection and cylinder integrals

The unit measure is the actual restriction of normalized additive Haar,
scaled by three-halves. Its finite projections are the independently
constructed uniform unit-seed PMFs.
-/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem padicThree_isUnit_iff_projection_ne_zero (x : ℤ_[3]) :
    IsUnit x ↔ PadicInt.toZModPow 1 x ≠ 0 := by
  have hz : PadicInt.toZModPow 1 x = 0 ↔ (3 : ℤ_[3]) ∣ x := by
    rw [← RingHom.mem_ker, kernel_three, Ideal.mem_span_singleton, pow_one]
  rw [← not_iff_not, PadicInt.not_isUnit_iff, not_not, hz,
    PadicInt.norm_lt_one_iff_dvd]
  norm_num

theorem padicThree_isUnit_iff_projection_val_mod_three (j : ℕ) (x : ℤ_[3]) :
    IsUnit x ↔ (PadicInt.toZModPow (j + 1) x).val % 3 ≠ 0 := by
  have hp : PadicInt.toZModPow 1 x =
      ((PadicInt.toZModPow (j + 1) x).val : ZMod (3 ^ 1)) := by
    rw [← padic_projection_reduce (show 1 ≤ j + 1 by omega) x]
    change (ZMod.castHom (pow_dvd_pow 3 (show 1 ≤ j + 1 by omega))
      (ZMod (3 ^ 1))) (PadicInt.toZModPow (j + 1) x) = _
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [padicThree_isUnit_iff_projection_ne_zero, hp]
  exact not_congr ((ZMod.natCast_eq_zero_iff _ _).trans (by
    simp only [pow_one, Nat.dvd_iff_mod_eq_zero]))

theorem padicThree_units_measurable : MeasurableSet {x : ℤ_[3] | IsUnit x} := by
  have hset : {x : ℤ_[3] | IsUnit x} =
      {x : ℤ_[3] | PadicInt.toZModPow 1 x = 0}ᶜ := by
    ext x
    exact padicThree_isUnit_iff_projection_ne_zero x
  rw [hset]
  exact (padic_cylinder_measurable 1 0).compl

theorem padicThreeHaar_units :
    padicThreeHaar {x : ℤ_[3] | IsUnit x} = 2 / 3 := by
  have hset : {x : ℤ_[3] | IsUnit x} =
      {x : ℤ_[3] | PadicInt.toZModPow 1 x = 0}ᶜ := by
    ext x
    exact padicThree_isUnit_iff_projection_ne_zero x
  rw [hset, measure_compl (padic_cylinder_measurable 1 0) (measure_ne_top _ _),
    measure_univ, padicThreeHaar_cylinder]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr (by norm_num)) (by simp)]
  norm_num

noncomputable def padicThreeUnitHaar : Measure ℤ_[3] :=
  (3 / 2 : ℝ≥0∞) • padicThreeHaar.restrict {x : ℤ_[3] | IsUnit x}

instance padicThreeUnitHaar_isProbabilityMeasure : IsProbabilityMeasure padicThreeUnitHaar where
  measure_univ := by
    rw [padicThreeUnitHaar, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, padicThreeHaar_units]
    change (3 / 2 : ℝ≥0∞) * (2 / 3) = 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num

theorem padicThreeUnitHaar_cylinder (j : ℕ) (y : ZMod (3 ^ (j + 1))) :
    padicThreeUnitHaar {x : ℤ_[3] | PadicInt.toZModPow (j + 1) x = y} =
      unitSourceUniformSeed j y := by
  classical
  rw [padicThreeUnitHaar, Measure.smul_apply,
    Measure.restrict_apply (padic_cylinder_measurable (j + 1) y),
    unitSourceUniformSeed_apply]
  by_cases hy : y.val % 3 = 0
  · rw [if_pos hy]
    have hset : {x : ℤ_[3] | PadicInt.toZModPow (j + 1) x = y} ∩
        {x : ℤ_[3] | IsUnit x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hu⟩
      change PadicInt.toZModPow (j + 1) x = y at hx
      have h := (padicThree_isUnit_iff_projection_val_mod_three j x).mp hu
      exact h (by simpa only [hx] using hy)
    simp only [hset, measure_empty, smul_zero]
  · rw [if_neg hy]
    have hset : {x : ℤ_[3] | PadicInt.toZModPow (j + 1) x = y} ∩
        {x : ℤ_[3] | IsUnit x} =
        {x : ℤ_[3] | PadicInt.toZModPow (j + 1) x = y} := by
      apply Set.inter_eq_left.mpr
      intro x hx
      change PadicInt.toZModPow (j + 1) x = y at hx
      apply (padicThree_isUnit_iff_projection_val_mod_three j x).mpr
      simpa only [hx] using hy
    rw [hset, padicThreeHaar_cylinder]
    change (3 / 2 : ℝ≥0∞) * (3 ^ (j + 1))⁻¹ = (2 * 3 ^ j)⁻¹
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, pow_succ]
    field_simp

theorem padicThreeUnitHaar_projection_eq_uniformSeed (j : ℕ) :
    Measure.map (PadicInt.toZModPow (j + 1)) padicThreeUnitHaar =
      (unitSourceUniformSeed j).toMeasure := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.map_apply (padic_projection_measurable (j + 1)) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact padicThreeUnitHaar_cylinder j y

theorem integral_padicThreeUnitHaar_cylinder (j : ℕ) (f : ZMod (3 ^ (j + 1)) → ℝ) :
    (∫ x : ℤ_[3], f (PadicInt.toZModPow (j + 1) x) ∂padicThreeUnitHaar) =
      ∑ y : ZMod (3 ^ (j + 1)), (unitSourceUniformSeed j y).toReal * f y := by
  rw [← integral_map (padic_projection_measurable (j + 1)).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    padicThreeUnitHaar_projection_eq_uniformSeed, PMF.integral_eq_sum]
  rfl

#print axioms padicThreeUnitHaar_projection_eq_uniformSeed
#print axioms integral_padicThreeUnitHaar_cylinder

end Erdos1135.Tao
