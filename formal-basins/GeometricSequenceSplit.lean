import CanonicalSyracuseRecursion
import Mathlib.Probability.Independence.Process

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic

theorem half_geometric_memoryless :
    halfGeometricMeasure =
      (1 / 2 : ℝ≥0∞) • Measure.dirac 0 +
        (1 / 2 : ℝ≥0∞) • halfGeometricMeasure.map Nat.succ := by
  have hh : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_of_countable Nat.succ) (measurableSet_singleton n)]
  cases n with
  | zero =>
    have he : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext a; simp
    rw [he, measure_empty, half_geometric_singleton]
    simp
  | succ n =>
    have he : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext a; simp
    rw [he, half_geometric_singleton, half_geometric_singleton]
    have hd : Measure.dirac (0 : ℕ) {n + 1} = 0 := by simp
    rw [hd]
    simp only [smul_eq_mul, mul_zero, zero_add]
    rw [pow_succ, ENNReal.ofReal_mul (by positivity)]
    rw [hh, mul_comm]

theorem geometric_coordinates_independent :
    iIndepFun (fun i : ℕ => fun f : ℕ → ℕ => f i) geometricSequenceMeasure := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ => halfGeometricMeasure) (fun _ => measurable_id)

theorem geometric_coordinate_law (i : ℕ) :
    geometricSequenceMeasure.map (fun f : ℕ → ℕ => f i) = halfGeometricMeasure :=
  Measure.infinitePi_map_eval _ i

theorem geometric_tail_law :
    geometricSequenceMeasure.map (fun f : ℕ → ℕ => fun i => f (i + 1)) =
      geometricSequenceMeasure := by
  have hi := geometric_coordinates_independent.precomp Nat.succ_injective
  have hl := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i : ℕ => measurable_pi_apply (i + 1))).mp hi
  simpa only [geometric_coordinate_law] using hl

theorem geometric_head_tail_independent :
    IndepFun (fun f : ℕ → ℕ => f 0) (fun f : ℕ → ℕ => fun i => f (i + 1))
      geometricSequenceMeasure := by
  apply IndepFun.indepFun_process (measurable_pi_apply 0).aemeasurable
    (fun i : ℕ => measurable_pi_apply (i + 1))
  intro I
  have hd : Disjoint ({0} : Finset ℕ) (I.image Nat.succ) := by simp
  have hi := geometric_coordinates_independent.indepFun_finset {0} (I.image Nat.succ) hd
    (fun i => measurable_pi_apply i)
  exact hi.comp
    (show Measurable (fun g : ({0} : Finset ℕ) → ℕ => g ⟨0, by simp⟩) from by fun_prop)
    (show Measurable (fun g : (I.image Nat.succ) → ℕ => fun i : I =>
      g ⟨i + 1, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩) from by fun_prop)

theorem geometric_head_tail_law :
    geometricSequenceMeasure.map (fun f : ℕ → ℕ => (f 0, fun i => f (i + 1))) =
      halfGeometricMeasure.prod geometricSequenceMeasure := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable
    (show Measurable (fun f : ℕ → ℕ => fun i => f (i + 1)) from by fun_prop).aemeasurable).mp
      geometric_head_tail_independent, geometric_coordinate_law, geometric_tail_law]

#print axioms half_geometric_memoryless
#print axioms geometric_tail_law
#print axioms geometric_head_tail_independent
#print axioms geometric_head_tail_law

end CollatzCylinderPacking.Arithmetic
