import CanonicalCylinderRecursion

set_option autoImplicit false
open MeasureTheory Classical

namespace CollatzCylinderPacking.Arithmetic

noncomputable def canonicalPadicRho (k : ℕ) (v : ℤ_[3]) : ℝ :=
  (3 : ℝ) ^ k * (canonicalSyracuseMeasure
    {x : ℤ_[3] | PadicInt.toZModPow k x = PadicInt.toZModPow k v}).toReal

theorem canonicalPadicRho_natCast (k N : ℕ) :
    canonicalPadicRho k (N : ℤ_[3]) = canonicalRho k N := by
  simp only [canonicalPadicRho, canonicalRho, map_natCast]

theorem syracuseJ_preimage_of_mod_three {v : ℤ_[3]}
    (hv : PadicInt.toZModPow 1 v = 2) : ∃ y : ℤ_[3], syracuseJ y = v := by
  have hp : PadicInt.toZModPow 1 (2 * v) = PadicInt.toZModPow 1 1 := by
    simp only [map_mul, map_ofNat, map_one, hv]
    decide
  have hd := (padic_projection_eq_iff_power_dvd 1 (2 * v) 1).mp hp
  rw [pow_one] at hd
  obtain ⟨y, hy⟩ := hd
  refine ⟨y, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ_[3]) ≠ 0)
  rw [syracuseJ_double]
  linear_combination -hy

noncomputable def padicOddPredecessor (v : ℤ_[3]) : ℤ_[3] :=
  if h : PadicInt.toZModPow 1 v = 2 then
    Classical.choose (syracuseJ_preimage_of_mod_three h) else 0

theorem syracuseJ_padicOddPredecessor {v : ℤ_[3]}
    (hv : PadicInt.toZModPow 1 v = 2) : syracuseJ (padicOddPredecessor v) = v := by
  simp only [padicOddPredecessor, dif_pos hv]
  exact Classical.choose_spec (syracuseJ_preimage_of_mod_three hv)

theorem padicOddPredecessor_equation {v : ℤ_[3]}
    (hv : PadicInt.toZModPow 1 v = 2) : 3 * padicOddPredecessor v = 2 * v - 1 := by
  have h := syracuseJ_double (padicOddPredecessor v)
  rw [syracuseJ_padicOddPredecessor hv] at h
  linear_combination -h

theorem syracuseJ_padic_cylinder_preimage {v : ℤ_[3]}
    (hv : PadicInt.toZModPow 1 v = 2) (k : ℕ) :
    {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = PadicInt.toZModPow (k + 1) v} =
      {x : ℤ_[3] | PadicInt.toZModPow k x = PadicInt.toZModPow k (padicOddPredecessor v)} := by
  ext x
  simp only [Set.mem_setOf_eq]
  have h := syracuseJ_projection_eq_iff k x (padicOddPredecessor v)
  simpa only [syracuseJ_padicOddPredecessor hv] using h

theorem syracuseJ_padic_cylinder_preimage_empty {v : ℤ_[3]}
    (hv : PadicInt.toZModPow 1 v ≠ 2) (k : ℕ) :
    {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = PadicInt.toZModPow (k + 1) v} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hr := padic_projection_refines (by omega : 1 ≤ k + 1) hx
  rw [syracuseJ_mod_three] at hr
  exact hv hr.symm

/-- The pointwise stationary recursion on every 3-adic integer; on the
admissible class the predecessor satisfies 3y = 2v - 1. -/
theorem canonicalPadicRho_successor_recursion (k : ℕ) (v : ℤ_[3]) :
    canonicalPadicRho (k + 1) v = (1 / 2 : ℝ) * canonicalPadicRho (k + 1) (2 * v) +
      (3 / 2 : ℝ) * (if PadicInt.toZModPow 1 v = 2 then
        canonicalPadicRho k (padicOddPredecessor v) else 0) := by
  have h := stationary_cylinder_real_recursion canonicalSyracuseMeasure
    canonical_is_syracuse_stationary (k + 1) (PadicInt.toZModPow (k + 1) v)
  have he : (2 : ZMod (3 ^ (k + 1))) * PadicInt.toZModPow (k + 1) v =
      PadicInt.toZModPow (k + 1) (2 * v) := by rw [map_mul, map_ofNat]
  rw [he] at h
  by_cases hv : PadicInt.toZModPow 1 v = 2
  · rw [syracuseJ_padic_cylinder_preimage hv k] at h
    rw [if_pos hv]
    unfold canonicalPadicRho
    rw [h, pow_succ]
    ring
  · rw [syracuseJ_padic_cylinder_preimage_empty hv k, measure_empty, ENNReal.toReal_zero] at h
    rw [if_neg hv]
    unfold canonicalPadicRho
    rw [h]
    ring

#print axioms canonicalPadicRho_natCast
#print axioms padicOddPredecessor_equation
#print axioms canonicalPadicRho_successor_recursion

end CollatzCylinderPacking.Arithmetic
