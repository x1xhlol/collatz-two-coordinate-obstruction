import PadicCylinderDetermining

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic

theorem padic_projection_measurable (k : ℕ) :
    @Measurable ℤ_[3] (ZMod (3 ^ k)) padicThreeMeasurableSpace ⊤
      (PadicInt.toZModPow k) := by
  apply @measurable_to_countable (ZMod (3 ^ k)) ℤ_[3] ⊤ _ padicThreeMeasurableSpace
  intro x
  exact padic_cylinder_measurable k (PadicInt.toZModPow k x)

theorem padic_projection_map_eq (k : ℕ) (μ ν : Measure ℤ_[3])
    (h : ∀ v : ZMod (3 ^ k),
      μ {x | PadicInt.toZModPow k x = v} = ν {x | PadicInt.toZModPow k x = v}) :
    @Measure.map ℤ_[3] (ZMod (3 ^ k)) padicThreeMeasurableSpace ⊤
        (PadicInt.toZModPow k) μ =
      @Measure.map ℤ_[3] (ZMod (3 ^ k)) padicThreeMeasurableSpace ⊤
        (PadicInt.toZModPow k) ν := by
  letI : MeasurableSpace (ZMod (3 ^ k)) := ⊤
  letI : MeasurableSingletonClass (ZMod (3 ^ k)) := ⟨fun _ => trivial⟩
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (padic_projection_measurable k) (measurableSet_singleton v),
    Measure.map_apply (padic_projection_measurable k) (measurableSet_singleton v)]
  exact h v

theorem syracuseH_double (x : ℤ_[3]) : 2 * syracuseH x = x := by
  have hu : (2 : ℤ_[3]) * (↑(padicTwoUnit⁻¹) : ℤ_[3]) = 1 := by
    rw [← padicTwoUnit_coe]
    exact Units.mul_inv padicTwoUnit
  rw [syracuseH, ← mul_assoc, hu, one_mul]

theorem syracuseH_cylinder_preimage (k : ℕ) (v : ZMod (3 ^ k)) :
    {x : ℤ_[3] | PadicInt.toZModPow k (syracuseH x) = v} =
      {x : ℤ_[3] | PadicInt.toZModPow k x = 2 * v} := by
  ext x
  simp only [Set.mem_setOf_eq]
  have hd : (2 : ZMod (3 ^ k)) * PadicInt.toZModPow k (syracuseH x) =
      PadicInt.toZModPow k x := by
    rw [← map_ofNat (PadicInt.toZModPow k) 2, ← map_mul, syracuseH_double]
  constructor
  · intro h
    rw [← hd, h]
  · intro h
    have hu : (↑((powerTwoUnit k 1)⁻¹) : ZMod (3 ^ k)) * 2 = 1 := by
      have he : (powerTwoUnit k 1 : ZMod (3 ^ k)) = 2 := by
        rw [powerTwoUnit_coe, pow_one]
      rw [← he]
      exact Units.inv_mul (powerTwoUnit k 1)
    have hh := congrArg (fun z : ZMod (3 ^ k) => (↑((powerTwoUnit k 1)⁻¹)) * z)
      (hd.trans h)
    simpa only [← mul_assoc, hu, one_mul] using hh

theorem syracuseJ_projection_approximation (k : ℕ) (x : ℤ_[3]) :
    PadicInt.toZModPow (k + 1) (syracuseJ x) =
      PadicInt.toZModPow (k + 1) (syracuseJ (padicResidueApproximation k x)) := by
  have hi : x - padicResidueApproximation k x ∈
      (Ideal.span {(3 : ℤ_[3]) ^ k} : Ideal ℤ_[3]) := by
    rw [← kernel_three k, RingHom.mem_ker, map_sub, padicResidueApproximation,
      map_natCast, ZMod.natCast_zmod_val, sub_self]
  rcases Ideal.mem_span_singleton.mp hi with ⟨z, hz⟩
  have hj : syracuseJ x - syracuseJ (padicResidueApproximation k x) ∈
      (Ideal.span {(3 : ℤ_[3]) ^ (k + 1)} : Ideal ℤ_[3]) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(↑(padicTwoUnit⁻¹) : ℤ_[3]) * z, ?_⟩
    calc
      syracuseJ x - syracuseJ (padicResidueApproximation k x) =
          (↑(padicTwoUnit⁻¹) : ℤ_[3]) * 3 * (x - padicResidueApproximation k x) := by
        unfold syracuseJ
        ring
      _ = (3 : ℤ_[3]) ^ (k + 1) * ((↑(padicTwoUnit⁻¹) : ℤ_[3]) * z) := by
        rw [hz, pow_succ]
        ring
  rw [← kernel_three (k + 1), RingHom.mem_ker, map_sub] at hj
  exact sub_eq_zero.mp hj

/-- The J-preimage of a depth k+1 cylinder depends only on the depth k law. -/
theorem syracuseJ_cylinder_measure_eq (k : ℕ) (μ ν : Measure ℤ_[3])
    (h : ∀ w : ZMod (3 ^ k),
      μ {x | PadicInt.toZModPow k x = w} = ν {x | PadicInt.toZModPow k x = w})
    (v : ZMod (3 ^ (k + 1))) :
    μ {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = v} =
      ν {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = v} := by
  letI : MeasurableSpace (ZMod (3 ^ k)) := ⊤
  let s : Set (ZMod (3 ^ k)) :=
    {w | PadicInt.toZModPow (k + 1) (syracuseJ (w.val : ℤ_[3])) = v}
  have hs : MeasurableSet s := trivial
  have he := congrArg (fun ρ : Measure (ZMod (3 ^ k)) => ρ s) (padic_projection_map_eq k μ ν h)
  dsimp only at he
  rw [Measure.map_apply (padic_projection_measurable k) hs,
    Measure.map_apply (padic_projection_measurable k) hs] at he
  have hp : (PadicInt.toZModPow k) ⁻¹' s =
      {x : ℤ_[3] | PadicInt.toZModPow (k + 1) (syracuseJ x) = v} := by
    ext x
    change PadicInt.toZModPow (k + 1) (syracuseJ (padicResidueApproximation k x)) = v ↔ _
    rw [← syracuseJ_projection_approximation]
    rfl
  simpa only [hp] using he

#print axioms padic_projection_map_eq
#print axioms syracuseH_cylinder_preimage
#print axioms syracuseJ_projection_approximation
#print axioms syracuseJ_cylinder_measure_eq

end CollatzCylinderPacking.Arithmetic
