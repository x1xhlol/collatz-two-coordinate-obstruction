import UnitHaarCylinder
import CanonicalCylinderRecursion

/-!
# A positive-exponent affine branch on the actual 3-adic integers

The branch loses exactly one residue digit. Its full image is one
depth-one cylinder, and the image of each cylinder gains one digit.
-/

set_option autoImplicit false
open MeasureTheory
open CollatzCylinderPacking.Arithmetic

namespace Erdos1135.Tao

noncomputable def padicAffineBranch (a : ℕ+) (x : ℤ_[3]) : ℤ_[3] :=
  (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a : ℕ) * (1 + 3 * x)

theorem padicAffineBranch_continuous (a : ℕ+) : Continuous (padicAffineBranch a) := by
  unfold padicAffineBranch
  fun_prop

theorem padicAffineBranch_measurable (a : ℕ+) : Measurable (padicAffineBranch a) :=
  (padicAffineBranch_continuous a).measurable

theorem padicAffineBranch_injective (a : ℕ+) : Function.Injective (padicAffineBranch a) := by
  intro x y h
  have hu : (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a : ℕ) ≠ 0 :=
    pow_ne_zero _ (Units.ne_zero _)
  have h' := mul_left_cancel₀ hu h
  exact mul_left_cancel₀ (by norm_num : (3 : ℤ_[3]) ≠ 0) (add_left_cancel h')

theorem padicAffineBranch_projection_eq_iff (a : ℕ+) (k : ℕ) (x y : ℤ_[3]) :
    PadicInt.toZModPow (k + 1) (padicAffineBranch a x) =
      PadicInt.toZModPow (k + 1) (padicAffineBranch a y) ↔
      PadicInt.toZModPow k x = PadicInt.toZModPow k y := by
  rw [padic_projection_eq_iff_power_dvd, padic_projection_eq_iff_power_dvd]
  have he : padicAffineBranch a x - padicAffineBranch a y =
      (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a : ℕ) * (3 * (x - y)) := by
    unfold padicAffineBranch
    ring
  rw [he, ((padicTwoUnit⁻¹).isUnit.pow (a : ℕ)).dvd_mul_left,
    pow_succ, mul_comm ((3 : ℤ_[3]) ^ k) 3]
  exact mul_dvd_mul_iff_left (by norm_num : (3 : ℤ_[3]) ≠ 0)

theorem padicAffineBranch_range (a : ℕ+) :
    Set.range (padicAffineBranch a) =
      {y : ℤ_[3] | PadicInt.toZModPow 1 y =
        PadicInt.toZModPow 1 (padicAffineBranch a 0)} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (padicAffineBranch_projection_eq_iff a 0 x 0).mpr
      (by change (_ : ZMod 1) = _; exact Subsingleton.elim _ _)
  · intro hy
    have hd := (padic_projection_eq_iff_power_dvd 1 y (padicAffineBranch a 0)).mp hy
    rw [pow_one] at hd
    obtain ⟨z, hz⟩ := hd
    refine ⟨(padicTwoUnit : ℤ_[3]) ^ (a : ℕ) * z, ?_⟩
    have hu : (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a : ℕ) *
        (padicTwoUnit : ℤ_[3]) ^ (a : ℕ) = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    have he : padicAffineBranch a ((padicTwoUnit : ℤ_[3]) ^ (a : ℕ) * z) =
        padicAffineBranch a 0 + 3 * z := by
      unfold padicAffineBranch
      calc
        _ = (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a : ℕ) + 3 *
          ((↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a : ℕ) *
            (padicTwoUnit : ℤ_[3]) ^ (a : ℕ)) * z := by ring
        _ = _ := by rw [hu]; ring
    rw [he]
    linear_combination -hz

theorem padicAffineBranch_range_measurable (a : ℕ+) :
    MeasurableSet (Set.range (padicAffineBranch a)) := by
  rw [padicAffineBranch_range]
  exact padic_cylinder_measurable 1 _

theorem padicAffineBranch_image_cylinder (a : ℕ+) (k : ℕ) (x : ℤ_[3]) :
    padicAffineBranch a '' {y : ℤ_[3] | PadicInt.toZModPow k y = PadicInt.toZModPow k x} =
      {y : ℤ_[3] | PadicInt.toZModPow (k + 1) y =
        PadicInt.toZModPow (k + 1) (padicAffineBranch a x)} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (padicAffineBranch_projection_eq_iff a k z x).mpr hz
  · intro hy
    have hr : y ∈ Set.range (padicAffineBranch a) := by
      rw [padicAffineBranch_range]
      exact (padic_projection_refines (by omega : 1 ≤ k + 1) hy).trans
        ((padicAffineBranch_projection_eq_iff a 0 x 0).mpr
          (by change (_ : ZMod 1) = _; exact Subsingleton.elim _ _))
    obtain ⟨z, rfl⟩ := hr
    exact ⟨z, (padicAffineBranch_projection_eq_iff a k z x).mp hy, rfl⟩

theorem padicThree_units_eq_two_cylinders :
    {x : ℤ_[3] | IsUnit x} =
      {x : ℤ_[3] | PadicInt.toZModPow 1 x = PadicInt.toZModPow 1 (1 : ℤ_[3])} ∪
      {x : ℤ_[3] | PadicInt.toZModPow 1 x = PadicInt.toZModPow 1 (2 : ℤ_[3])} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, padicThree_isUnit_iff_projection_ne_zero,
    map_one, map_ofNat]
  have h : ∀ z : ZMod 3, z ≠ 0 ↔ z = 1 ∨ z = 2 := by decide
  exact h _

theorem padicAffineBranch_image_units (a : ℕ+) :
    padicAffineBranch a '' {x : ℤ_[3] | IsUnit x} =
      {y : ℤ_[3] | PadicInt.toZModPow 2 y =
        PadicInt.toZModPow 2 (padicAffineBranch a 1)} ∪
      {y : ℤ_[3] | PadicInt.toZModPow 2 y =
        PadicInt.toZModPow 2 (padicAffineBranch a 2)} := by
  rw [padicThree_units_eq_two_cylinders, Set.image_union,
    padicAffineBranch_image_cylinder, padicAffineBranch_image_cylinder]

theorem padicAffineBranch_image_units_measurable (a : ℕ+) :
    MeasurableSet (padicAffineBranch a '' {x : ℤ_[3] | IsUnit x}) := by
  rw [padicAffineBranch_image_units]
  exact (padic_cylinder_measurable 2 _).union (padic_cylinder_measurable 2 _)

theorem padicAffineBranch_image_unit_cylinders_disjoint (a : ℕ+) :
    Disjoint
      {y : ℤ_[3] | PadicInt.toZModPow 2 y =
        PadicInt.toZModPow 2 (padicAffineBranch a 1)}
      {y : ℤ_[3] | PadicInt.toZModPow 2 y =
        PadicInt.toZModPow 2 (padicAffineBranch a 2)} := by
  apply Set.disjoint_left.mpr
  intro y h1 h2
  have h := (padicAffineBranch_projection_eq_iff a 1 1 2).mp (h1.symm.trans h2)
  simp only [map_one, map_ofNat] at h
  exact (by decide : (1 : ZMod (3 ^ 1)) ≠ 2) h

theorem padicAffineBranch_isUnit (a : ℕ+) (x : ℤ_[3]) : IsUnit (padicAffineBranch a x) := by
  rw [padicThree_isUnit_iff_projection_ne_zero]
  have hr : padicAffineBranch a x ∈ Set.range (padicAffineBranch a) := ⟨x, rfl⟩
  rw [padicAffineBranch_range] at hr
  change PadicInt.toZModPow 1 (padicAffineBranch a x) = _ at hr
  rw [hr]
  apply (padicThree_isUnit_iff_projection_ne_zero _).mp
  simpa only [padicAffineBranch, mul_zero, add_zero, mul_one] using
    (padicTwoUnit⁻¹).isUnit.pow (a : ℕ)

#print axioms padicAffineBranch_range
#print axioms padicAffineBranch_image_cylinder
#print axioms padicAffineBranch_image_units

end Erdos1135.Tao
