import PadicAffineBranch

/-!
# Actual Haar pushforward under one affine branch

Cylinder geometry and actual Haar cylinder probabilities determine the
pushforward. No measure-scaling identity is assumed.
-/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

theorem padicAffineBranch_range_haar (a : ℕ+) :
    padicThreeHaar (Set.range (padicAffineBranch a)) = 1 / 3 := by
  rw [padicAffineBranch_range, padicThreeHaar_cylinder]
  norm_num

theorem padicAffineBranch_map_haar (a : ℕ+) :
    Measure.map (padicAffineBranch a) padicThreeHaar =
      (3 : ℝ≥0∞) • padicThreeHaar.restrict (Set.range (padicAffineBranch a)) := by
  let ν := (3 : ℝ≥0∞) • padicThreeHaar.restrict (Set.range (padicAffineBranch a))
  haveI : IsProbabilityMeasure ν := ⟨by
    change 3 * padicThreeHaar.restrict (Set.range (padicAffineBranch a)) Set.univ = 1
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      padicAffineBranch_range_haar]
    rw [one_div]
    exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness)⟩
  haveI : IsProbabilityMeasure (Measure.map (padicAffineBranch a) padicThreeHaar) :=
    Measure.isProbabilityMeasure_map (padicAffineBranch_measurable a).aemeasurable
  change Measure.map (padicAffineBranch a) padicThreeHaar = ν
  apply padic_probability_eq_of_cylinders
  intro k v
  cases k with
  | zero =>
      have hset : {x : ℤ_[3] | PadicInt.toZModPow 0 x = v} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        change (_ : ZMod 1) = _
        exact Subsingleton.elim _ _
      rw [hset, measure_univ, measure_univ]
  | succ k =>
      by_cases hn : ({y : ℤ_[3] | PadicInt.toZModPow (k + 1) y = v} ∩
          Set.range (padicAffineBranch a)).Nonempty
      · obtain ⟨w, hw, z, rfl⟩ := hn
        change PadicInt.toZModPow (k + 1) (padicAffineBranch a z) = v at hw
        rw [← hw]
        have hpre : (padicAffineBranch a) ⁻¹'
            {y : ℤ_[3] | PadicInt.toZModPow (k + 1) y =
              PadicInt.toZModPow (k + 1) (padicAffineBranch a z)} =
            {x : ℤ_[3] | PadicInt.toZModPow k x = PadicInt.toZModPow k z} := by
          ext x
          exact padicAffineBranch_projection_eq_iff a k x z
        have hsub : {y : ℤ_[3] | PadicInt.toZModPow (k + 1) y =
              PadicInt.toZModPow (k + 1) (padicAffineBranch a z)} ⊆
            Set.range (padicAffineBranch a) := by
          rw [← padicAffineBranch_image_cylinder]
          exact Set.image_subset_range _ _
        rw [Measure.map_apply (padicAffineBranch_measurable a)
          (padic_cylinder_measurable (k + 1) _), hpre, padicThreeHaar_cylinder]
        change _ = 3 * padicThreeHaar.restrict (Set.range (padicAffineBranch a)) _
        rw [Measure.restrict_apply (padic_cylinder_measurable (k + 1) _),
          Set.inter_eq_left.mpr hsub, padicThreeHaar_cylinder]
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, pow_succ]
        field_simp
      · have hinter : {y : ℤ_[3] | PadicInt.toZModPow (k + 1) y = v} ∩
            Set.range (padicAffineBranch a) = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
        have hpre : (padicAffineBranch a) ⁻¹'
            {y : ℤ_[3] | PadicInt.toZModPow (k + 1) y = v} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hn ⟨padicAffineBranch a x, hx, ⟨x, rfl⟩⟩
        rw [Measure.map_apply (padicAffineBranch_measurable a)
          (padic_cylinder_measurable (k + 1) _), hpre, measure_empty]
        change _ = 3 * padicThreeHaar.restrict (Set.range (padicAffineBranch a)) _
        rw [Measure.restrict_apply (padic_cylinder_measurable (k + 1) _),
          hinter, measure_empty, mul_zero]

theorem padicAffineBranch_image_units_haar (a : ℕ+) :
    padicThreeHaar (padicAffineBranch a '' {x : ℤ_[3] | IsUnit x}) = 2 / 9 := by
  rw [padicAffineBranch_image_units,
    measure_union (padicAffineBranch_image_unit_cylinders_disjoint a)
      (padic_cylinder_measurable 2 _),
    padicThreeHaar_cylinder, padicThreeHaar_cylinder]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

theorem padicAffineBranch_map_unitHaar (a : ℕ+) :
    Measure.map (padicAffineBranch a) padicThreeUnitHaar =
      (9 / 2 : ℝ≥0∞) • padicThreeHaar.restrict
        (padicAffineBranch a '' {x : ℤ_[3] | IsUnit x}) := by
  have hpre : (padicAffineBranch a) ⁻¹'
      (padicAffineBranch a '' {x : ℤ_[3] | IsUnit x}) = {x : ℤ_[3] | IsUnit x} :=
    (padicAffineBranch_injective a).preimage_image _
  have hrestrict := Measure.restrict_map (μ := padicThreeHaar)
    (padicAffineBranch_measurable a) (padicAffineBranch_image_units_measurable a)
  rw [hpre, padicAffineBranch_map_haar, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset (Set.image_subset_range _ _)] at hrestrict
  rw [padicThreeUnitHaar, Measure.map_smul, ← hrestrict, smul_smul]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

theorem padicAffineBranch_map_unitHaar_eq_restrict (a : ℕ+) :
    Measure.map (padicAffineBranch a) padicThreeUnitHaar =
      (3 : ℝ≥0∞) • padicThreeUnitHaar.restrict
        (padicAffineBranch a '' {x : ℤ_[3] | IsUnit x}) := by
  have hsub : padicAffineBranch a '' {x : ℤ_[3] | IsUnit x} ⊆
      {x : ℤ_[3] | IsUnit x} := by
    rintro y ⟨x, _, rfl⟩
    exact padicAffineBranch_isUnit a x
  rw [padicAffineBranch_map_unitHaar, padicThreeUnitHaar,
    Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub, smul_smul]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

#print axioms padicAffineBranch_map_haar
#print axioms padicAffineBranch_map_unitHaar
#print axioms padicAffineBranch_map_unitHaar_eq_restrict

end Erdos1135.Tao
