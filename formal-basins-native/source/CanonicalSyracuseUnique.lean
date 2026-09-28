import SyracuseCylinderTransitions

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic

def IsSyracuseStationary (μ : Measure ℤ_[3]) : Prop :=
  μ = (1 / 2 : ℝ≥0∞) • μ.map syracuseH + (1 / 2 : ℝ≥0∞) • μ.map syracuseJ

theorem canonical_is_syracuse_stationary : IsSyracuseStationary canonicalSyracuseMeasure :=
  canonical_syracuse_stationarity

theorem stationary_cylinder_real_recursion (μ : Measure ℤ_[3]) [IsProbabilityMeasure μ]
    (hμ : IsSyracuseStationary μ) (k : ℕ) (v : ZMod (3 ^ k)) :
    (μ {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal =
      (1 / 2 : ℝ) * (μ {x : ℤ_[3] | PadicInt.toZModPow k x = 2 * v}).toReal +
        (1 / 2 : ℝ) * (μ {x : ℤ_[3] | PadicInt.toZModPow k (syracuseJ x) = v}).toReal := by
  have he := congrArg (fun ρ : Measure ℤ_[3] => ρ {x | PadicInt.toZModPow k x = v}) hμ
  dsimp only at he
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply syracuseH_measurable (padic_cylinder_measurable k v),
    Measure.map_apply syracuseJ_measurable (padic_cylinder_measurable k v)] at he
  change μ {x | PadicInt.toZModPow k x = v} =
    (1 / 2 : ℝ≥0∞) * μ {x | PadicInt.toZModPow k (syracuseH x) = v} +
      (1 / 2 : ℝ≥0∞) * μ {x | PadicInt.toZModPow k (syracuseJ x) = v} at he
  rw [syracuseH_cylinder_preimage] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _))
    (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul] at hr
  norm_num at hr
  exact hr

theorem finite_half_contraction_zero {α : Type*} [Fintype α] [Nonempty α]
    (d : α → ℝ) (T : α → α) (h : ∀ a, d a = (1 / 2 : ℝ) * d (T a)) :
    ∀ a, d a = 0 := by
  classical
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun a => |d a|)
  have hb (a : α) : |d a| ≤ M :=
    Finset.le_sup' (f := fun a => |d a|) (Finset.mem_univ a)
  have hm : M ≤ (1 / 2 : ℝ) * M := by
    apply (Finset.sup'_le_iff Finset.univ_nonempty (fun a => |d a|)).mpr
    intro a _
    rw [h a, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hb (T a)) (by norm_num)
  have hz : M ≤ 0 := by linarith
  intro a
  exact abs_eq_zero.mp (le_antisymm ((hb a).trans hz) (abs_nonneg _))

/-- H/J-stationary probability measures agree at each finite residue depth. -/
theorem stationary_probability_cylinders_eq (μ ν : Measure ℤ_[3])
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsSyracuseStationary μ) (hν : IsSyracuseStationary ν) :
    ∀ (k : ℕ) (v : ZMod (3 ^ k)),
      μ {x | PadicInt.toZModPow k x = v} = ν {x | PadicInt.toZModPow k x = v} := by
  intro k
  induction k with
  | zero =>
    intro v
    haveI : Subsingleton (ZMod (3 ^ 0)) := by
      change Subsingleton (ZMod 1)
      infer_instance
    have hs : {x : ℤ_[3] | PadicInt.toZModPow 0 x = v} = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      exact Subsingleton.elim _ _
    rw [hs, measure_univ, measure_univ]
  | succ k ih =>
    let d : ZMod (3 ^ (k + 1)) → ℝ := fun v =>
      (μ {x | PadicInt.toZModPow (k + 1) x = v}).toReal -
        (ν {x | PadicInt.toZModPow (k + 1) x = v}).toReal
    have hd (v : ZMod (3 ^ (k + 1))) : d v = (1 / 2 : ℝ) * d (2 * v) := by
      have h1 := stationary_cylinder_real_recursion μ hμ (k + 1) v
      have h2 := stationary_cylinder_real_recursion ν hν (k + 1) v
      have hj := syracuseJ_cylinder_measure_eq k μ ν ih v
      rw [hj] at h1
      dsimp only [d]
      linarith
    have hz := finite_half_contraction_zero d (fun v => 2 * v) hd
    intro v
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp
    exact sub_eq_zero.mp (hz v)

/-- There is at most one H/J-stationary Borel probability measure on ℤ₃. -/
theorem syracuse_stationary_probability_unique (μ ν : Measure ℤ_[3])
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsSyracuseStationary μ) (hν : IsSyracuseStationary ν) : μ = ν :=
  padic_probability_eq_of_cylinders μ ν (stationary_probability_cylinders_eq μ ν hμ hν)

/-- The canonical Syracuse series law is the unique H/J-stationary probability measure. -/
theorem eq_canonical_of_syracuse_stationary (μ : Measure ℤ_[3]) [IsProbabilityMeasure μ]
    (hμ : IsSyracuseStationary μ) : μ = canonicalSyracuseMeasure :=
  syracuse_stationary_probability_unique μ canonicalSyracuseMeasure hμ canonical_is_syracuse_stationary

#print axioms stationary_cylinder_real_recursion
#print axioms finite_half_contraction_zero
#print axioms stationary_probability_cylinders_eq
#print axioms syracuse_stationary_probability_unique
#print axioms eq_canonical_of_syracuse_stationary

end CollatzCylinderPacking.Arithmetic
