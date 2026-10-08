import CanonicalSyracuseUnique
import CanonicalCylinderAbel
import ActualInverseOperator

set_option autoImplicit false
open MeasureTheory

namespace CollatzCylinderPacking.Arithmetic

theorem padic_projection_eq_iff_power_dvd (k : ℕ) (x y : ℤ_[3]) :
    PadicInt.toZModPow k x = PadicInt.toZModPow k y ↔ (3 : ℤ_[3]) ^ k ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, kernel_three,
    Ideal.mem_span_singleton]

theorem padic_three_projection_cancel (k : ℕ) (x y : ℤ_[3]) :
    PadicInt.toZModPow (k + 1) (3 * x) = PadicInt.toZModPow (k + 1) (3 * y) ↔
      PadicInt.toZModPow k x = PadicInt.toZModPow k y := by
  rw [padic_projection_eq_iff_power_dvd, padic_projection_eq_iff_power_dvd]
  have h3 : (3 : ℤ_[3]) ≠ 0 := by norm_num
  rw [← mul_sub, pow_succ, mul_comm ((3 : ℤ_[3]) ^ k) 3]
  exact mul_dvd_mul_iff_left h3

theorem syracuseJ_double (x : ℤ_[3]) : 2 * syracuseJ x = 1 + 3 * x := by
  change 2 * syracuseH (1 + 3 * x) = _
  exact syracuseH_double _

theorem syracuseJ_projection_eq_iff (k : ℕ) (x y : ℤ_[3]) :
    PadicInt.toZModPow (k + 1) (syracuseJ x) =
      PadicInt.toZModPow (k + 1) (syracuseJ y) ↔
      PadicInt.toZModPow k x = PadicInt.toZModPow k y := by
  have hu : (↑((powerTwoUnit (k + 1) 1)⁻¹) : ZMod (3 ^ (k + 1))) * 2 = 1 := by
    have he : (powerTwoUnit (k + 1) 1 : ZMod (3 ^ (k + 1))) = 2 := by
      rw [powerTwoUnit_coe, pow_one]
    rw [← he]
    exact Units.inv_mul _
  constructor
  · intro h
    apply (padic_three_projection_cancel k x y).mp
    have hh := congrArg (fun z : ZMod (3 ^ (k + 1)) => 2 * z) h
    simp only [← map_ofNat (PadicInt.toZModPow (k + 1)) 2, ← map_mul,
      syracuseJ_double, map_add, map_one] at hh
    exact add_left_cancel hh
  · intro h
    have hh := (padic_three_projection_cancel k x y).mpr h
    have he : (2 : ZMod (3 ^ (k + 1))) * PadicInt.toZModPow (k + 1) (syracuseJ x) =
        2 * PadicInt.toZModPow (k + 1) (syracuseJ y) := by
      simp only [← map_ofNat (PadicInt.toZModPow (k + 1)) 2, ← map_mul,
        syracuseJ_double, map_add, map_one]
      rw [hh]
    have hi := congrArg (fun z => (↑((powerTwoUnit (k + 1) 1)⁻¹) : ZMod (3 ^ (k + 1))) * z) he
    simpa only [← mul_assoc, hu, one_mul] using hi

theorem syracuseJ_oddPredecessor {N : ℕ} (hN : N % 3 = 2) :
    syracuseJ (oddPredecessor N : ℤ_[3]) = (N : ℤ_[3]) := by
  have hn : 3 * oddPredecessor N + 1 = 2 * N := by unfold oddPredecessor; omega
  have hr : (1 : ℤ_[3]) + 3 * (oddPredecessor N : ℤ_[3]) = 2 * (N : ℤ_[3]) := by
    exact_mod_cast (show 1 + 3 * oddPredecessor N = 2 * N by omega)
  have h := syracuseJ_double (oddPredecessor N : ℤ_[3])
  rw [hr] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ_[3]) ≠ 0) h

/-- The J-preimage of an admissible integer cylinder loses exactly one
3-adic digit, with its actual integer odd predecessor. -/
theorem syracuseJ_integer_cylinder_preimage {N : ℕ} (hN : N % 3 = 2) (k : ℕ) :
    {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = (N : ZMod (3 ^ (k + 1)))} =
      {x : ℤ_[3] | PadicInt.toZModPow k x = (oddPredecessor N : ZMod (3 ^ k))} := by
  ext x
  simp only [Set.mem_setOf_eq]
  have h := syracuseJ_projection_eq_iff k x (oddPredecessor N : ℤ_[3])
  simpa only [syracuseJ_oddPredecessor hN, map_natCast] using h

/-- A J-image always lies in the residue class two modulo three. -/
theorem syracuseJ_mod_three (x : ℤ_[3]) : PadicInt.toZModPow 1 (syracuseJ x) = 2 := by
  have h := congrArg (PadicInt.toZModPow 1) (syracuseJ_double x)
  norm_num only [map_mul, map_ofNat, map_add, map_one] at h ⊢
  have h3 : (3 : ZMod (3 ^ 1)) = 0 := by decide
  rw [h3, zero_mul, add_zero] at h
  have hh := congrArg (fun z : ZMod (3 ^ 1) => 2 * z) h
  have h4 : (4 : ZMod (3 ^ 1)) = 1 := by decide
  norm_num only [← mul_assoc, show (2 : ZMod (3 ^ 1)) * 2 = 4 by ring] at hh
  simpa only [h4, one_mul] using hh

theorem syracuseJ_integer_cylinder_preimage_empty {N : ℕ} (hN : N % 3 ≠ 2) (k : ℕ) :
    {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = (N : ZMod (3 ^ (k + 1)))} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hcast : PadicInt.toZModPow (k + 1) (syracuseJ x) =
      PadicInt.toZModPow (k + 1) (N : ℤ_[3]) := by simpa only [map_natCast] using hx
  have hr := padic_projection_refines (by omega : 1 ≤ k + 1) hcast
  rw [syracuseJ_mod_three, map_natCast] at hr
  have hv := congrArg ZMod.val hr
  norm_num [ZMod.val_natCast] at hv
  exact hN hv.symm

/-- The manuscript's explicit depth-lowering stationary cylinder recursion. -/
theorem canonicalRho_successor_recursion (k N : ℕ) :
    canonicalRho (k + 1) N = (1 / 2 : ℝ) * canonicalRho (k + 1) (2 * N) +
      (3 / 2 : ℝ) * (if N % 3 = 2 then canonicalRho k (oddPredecessor N) else 0) := by
  have h := stationary_cylinder_real_recursion canonicalSyracuseMeasure
    canonical_is_syracuse_stationary (k + 1) (N : ZMod (3 ^ (k + 1)))
  have he : (2 : ZMod (3 ^ (k + 1))) * (N : ZMod (3 ^ (k + 1))) =
      ((2 * N : ℕ) : ZMod (3 ^ (k + 1))) := by push_cast; rfl
  rw [he] at h
  by_cases hN : N % 3 = 2
  · rw [syracuseJ_integer_cylinder_preimage hN k] at h
    rw [if_pos hN]
    unfold canonicalRho
    rw [h, pow_succ]
    ring
  · rw [syracuseJ_integer_cylinder_preimage_empty hN k, measure_empty, ENNReal.toReal_zero] at h
    rw [if_neg hN]
    unfold canonicalRho
    rw [h]
    ring

#print axioms syracuseJ_integer_cylinder_preimage
#print axioms syracuseJ_integer_cylinder_preimage_empty
#print axioms canonicalRho_successor_recursion

end CollatzCylinderPacking.Arithmetic
