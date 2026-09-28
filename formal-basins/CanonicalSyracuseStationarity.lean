import GeometricSequenceSplit

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic

/-- Division by the unit two on the 3-adic integers. -/
noncomputable def syracuseH (x : ℤ_[3]) : ℤ_[3] :=
  (↑(padicTwoUnit⁻¹) : ℤ_[3]) * x

/-- The affine branch `(1 + 3*x)/2` on the 3-adic integers. -/
noncomputable def syracuseJ (x : ℤ_[3]) : ℤ_[3] :=
  (↑(padicTwoUnit⁻¹) : ℤ_[3]) * (1 + 3 * x)

noncomputable def geometricAffine (p : ℕ × ℤ_[3]) : ℤ_[3] :=
  (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (p.1 + 1) * (1 + 3 * p.2)

theorem syracuseH_measurable : Measurable syracuseH := by
  unfold syracuseH
  fun_prop

theorem syracuseJ_measurable : Measurable syracuseJ := by
  unfold syracuseJ
  fun_prop

theorem geometricAffine_measurable : Measurable geometricAffine := by
  apply measurable_from_prod_countable_right
  intro a
  have hc : Continuous (fun x : ℤ_[3] =>
      (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a + 1) * (1 + 3 * x)) := by fun_prop
  exact hc.measurable

theorem canonical_head_tail_pair_law :
    geometricSequenceMeasure.map (fun f : ℕ → ℕ =>
      (f 0, canonicalSyracuseVariable (fun i => f (i + 1)))) =
      halfGeometricMeasure.prod canonicalSyracuseMeasure := by
  have ht : Measurable (fun f : ℕ → ℕ => fun i => f (i + 1)) := by fun_prop
  have hpair := geometric_head_tail_independent.comp measurable_id canonical_variable_measurable
  have hl := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable
    (canonical_variable_measurable.comp ht).aemeasurable).mp hpair
  change geometricSequenceMeasure.map (fun f : ℕ → ℕ =>
      (f 0, canonicalSyracuseVariable (fun i => f (i + 1)))) = _ at hl
  rw [geometric_coordinate_law] at hl
  have he : geometricSequenceMeasure.map (canonicalSyracuseVariable ∘
      (fun f : ℕ → ℕ => fun i => f (i + 1))) = canonicalSyracuseMeasure := by
    rw [← Measure.map_map canonical_variable_measurable ht, geometric_tail_law]
    rfl
  simpa only [he] using hl

theorem canonical_geometric_affine_law :
    canonicalSyracuseMeasure =
      (halfGeometricMeasure.prod canonicalSyracuseMeasure).map geometricAffine := by
  have hp : Measurable (fun f : ℕ → ℕ =>
      (f 0, canonicalSyracuseVariable (fun i => f (i + 1)))) :=
    (measurable_pi_apply 0).prodMk (canonical_variable_measurable.comp (by fun_prop))
  rw [← canonical_head_tail_pair_law,
    Measure.map_map geometricAffine_measurable hp]
  unfold canonicalSyracuseMeasure
  congr 1
  funext f
  exact canonical_variable_affine_recursion f

theorem geometric_affine_zero_law :
    ((Measure.dirac 0).prod canonicalSyracuseMeasure).map geometricAffine =
      canonicalSyracuseMeasure.map syracuseJ := by
  rw [Measure.dirac_prod, Measure.map_map geometricAffine_measurable (by fun_prop)]
  congr 1
  funext x
  simp [geometricAffine, syracuseJ]

theorem geometric_affine_succ_law :
    ((halfGeometricMeasure.map Nat.succ).prod canonicalSyracuseMeasure).map geometricAffine =
      canonicalSyracuseMeasure.map syracuseH := by
  have hp : (halfGeometricMeasure.map Nat.succ).prod canonicalSyracuseMeasure =
      (halfGeometricMeasure.prod canonicalSyracuseMeasure).map (Prod.map Nat.succ id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map halfGeometricMeasure
      canonicalSyracuseMeasure (measurable_of_countable Nat.succ) measurable_id
  have hf : geometricAffine ∘ Prod.map Nat.succ id = syracuseH ∘ geometricAffine := by
    funext p
    simp only [Function.comp_def, geometricAffine, syracuseH, Prod.map_fst, Prod.map_snd,
      id_eq, pow_succ]
    ring
  rw [hp, Measure.map_map geometricAffine_measurable (by fun_prop), hf,
    ← Measure.map_map syracuseH_measurable geometricAffine_measurable,
    ← canonical_geometric_affine_law]

/-- The canonical Syracuse probability measure obeys the two-branch affine
stationarity equation as an equality of Borel measures. -/
theorem canonical_syracuse_stationarity :
    canonicalSyracuseMeasure =
      (1 / 2 : ℝ≥0∞) • canonicalSyracuseMeasure.map syracuseH +
        (1 / 2 : ℝ≥0∞) • canonicalSyracuseMeasure.map syracuseJ := by
  calc
    canonicalSyracuseMeasure =
        (halfGeometricMeasure.prod canonicalSyracuseMeasure).map geometricAffine :=
      canonical_geometric_affine_law
    _ = (1 / 2 : ℝ≥0∞) • canonicalSyracuseMeasure.map syracuseJ +
        (1 / 2 : ℝ≥0∞) • canonicalSyracuseMeasure.map syracuseH := by
      rw [half_geometric_memoryless, Measure.add_prod, Measure.prod_smul_left,
        Measure.prod_smul_left, Measure.map_add _ _ geometricAffine_measurable,
        Measure.map_smul, Measure.map_smul, geometric_affine_zero_law, geometric_affine_succ_law]
    _ = _ := add_comm _ _

#print axioms canonical_head_tail_pair_law
#print axioms canonical_geometric_affine_law
#print axioms canonical_syracuse_stationarity

end CollatzCylinderPacking.Arithmetic
