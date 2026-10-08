import UnitSourceUniformSeed
import SyracuseCylinderTransitions
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Additive Haar probabilities of actual 3-adic cylinders

The Haar measure is normalized on the full compact group. Its projection
to each finite residue ring is proved uniform using additive invariance.
-/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

noncomputable def padicThreeHaar : Measure ℤ_[3] :=
  Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts ℤ_[3])

instance padicThreeHaar_isProbabilityMeasure : IsProbabilityMeasure padicThreeHaar where
  measure_univ := by
    simpa only [padicThreeHaar, TopologicalSpace.PositiveCompacts.coe_top] using
      (Measure.addHaarMeasure_self
        (K₀ := (⊤ : TopologicalSpace.PositiveCompacts ℤ_[3])))

instance padicThreeHaar_isAddHaarMeasure : padicThreeHaar.IsAddHaarMeasure := by
  unfold padicThreeHaar
  infer_instance

theorem padicThreeProjection_surjective (k : ℕ) :
    Function.Surjective (PadicInt.toZModPow k : ℤ_[3] → ZMod (3 ^ k)) := by
  intro y
  refine ⟨(y.val : ℤ_[3]), ?_⟩
  simp only [map_natCast, ZMod.natCast_zmod_val]

theorem padicThreeHaar_projection_eq_uniform (k : ℕ) :
    Measure.map (PadicInt.toZModPow k) padicThreeHaar =
      (PMF.uniformOfFintype (ZMod (3 ^ k))).toMeasure := by
  classical
  let ν := Measure.map (PadicInt.toZModPow k) padicThreeHaar
  haveI : ν.IsAddLeftInvariant := isAddLeftInvariant_map
    (PadicInt.toZModPow k).toAddMonoidHom.toAddHom
    (padic_projection_measurable k) (padicThreeProjection_surjective k)
  have hν : ν Set.univ = 1 := by
    dsimp [ν]
    rw [Measure.map_apply (padic_projection_measurable k) MeasurableSet.univ]
    simp
  have hatom (y : ZMod (3 ^ k)) : ν {y} = ν {0} := by
    have h := measure_preimage_add ν y ({y} : Set (ZMod (3 ^ k)))
    have hset : (fun x : ZMod (3 ^ k) => y + x) ⁻¹' {y} = {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, add_eq_left]
    rw [hset] at h
    exact h.symm
  have hsum : ∑ y : ZMod (3 ^ k), ν {y} = 1 := by
    have h := sum_measure_singleton (μ := ν) (s := Finset.univ)
    simpa only [Finset.coe_univ, hν] using h
  have hmass : ν {0} = (Fintype.card (ZMod (3 ^ k)) : ℝ≥0∞)⁻¹ := by
    apply ENNReal.eq_inv_of_mul_eq_one_left
    simpa only [hatom, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum
  apply Measure.ext_of_singleton
  intro y
  change ν {y} = _
  rw [hatom, hmass, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

theorem padicThreeHaar_cylinder (k : ℕ) (y : ZMod (3 ^ k)) :
    padicThreeHaar {x : ℤ_[3] | PadicInt.toZModPow k x = y} =
      (3 ^ k : ℝ≥0∞)⁻¹ := by
  have h := congrArg (fun μ : Measure (ZMod (3 ^ k)) => μ {y})
    (padicThreeHaar_projection_eq_uniform k)
  dsimp only at h
  rw [Measure.map_apply (padic_projection_measurable k) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply] at h
  simpa only [ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using h

theorem integral_padicThreeHaar_cylinder (k : ℕ) (f : ZMod (3 ^ k) → ℝ) :
    (∫ x : ℤ_[3], f (PadicInt.toZModPow k x) ∂padicThreeHaar) =
      (∑ y : ZMod (3 ^ k), f y) / (3 : ℝ) ^ k := by
  rw [← integral_map (padic_projection_measurable k).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    padicThreeHaar_projection_eq_uniform, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ZMod.card, ENNReal.toReal_inv,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv, mul_comm]

#print axioms padicThreeHaar_projection_eq_uniform
#print axioms padicThreeHaar_cylinder
#print axioms integral_padicThreeHaar_cylinder

end Erdos1135.Tao
