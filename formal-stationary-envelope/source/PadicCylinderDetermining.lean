import CanonicalSyracuseStationarity

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace CollatzCylinderPacking.Arithmetic

def padicCylinders : Set (Set ℤ_[3]) :=
  {s | ∃ k : ℕ, ∃ v : ZMod (3 ^ k), s = {x | PadicInt.toZModPow k x = v}}

theorem padic_projection_reduce {k m : ℕ} (hkm : k ≤ m) (x : ℤ_[3]) :
    reduceResidue k m hkm (PadicInt.toZModPow m x) = PadicInt.toZModPow k x := by
  change ((ZMod.castHom (pow_dvd_pow 3 hkm) (ZMod (3 ^ k))).comp
    (PadicInt.toZModPow m)) x = _
  rw [PadicInt.zmod_cast_comp_toZModPow k m hkm]

theorem padic_projection_refines {k m : ℕ} (hkm : k ≤ m) {x y : ℤ_[3]}
    (he : PadicInt.toZModPow m x = PadicInt.toZModPow m y) :
    PadicInt.toZModPow k x = PadicInt.toZModPow k y := by
  rw [← padic_projection_reduce hkm x, ← padic_projection_reduce hkm y, he]

theorem padic_cylinders_piSystem : IsPiSystem padicCylinders := by
  rintro s ⟨k, v, rfl⟩ t ⟨m, w, rfl⟩ ⟨x, hx, hy⟩
  rcases le_total k m with hkm | hmk
  · refine ⟨m, w, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      exact (padic_projection_refines hkm (h.trans hy.symm)).trans hx
  · refine ⟨k, v, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      exact (padic_projection_refines hmk (h.trans hx.symm)).trans hy

noncomputable def padicResidueApproximation (k : ℕ) (x : ℤ_[3]) : ℤ_[3] :=
  ((PadicInt.toZModPow k x).val : ℤ_[3])

theorem padic_residue_approximation_bound (k : ℕ) (x : ℤ_[3]) :
    dist (padicResidueApproximation k x) x ≤ (1 / 3 : ℝ) ^ k := by
  have hi : x - padicResidueApproximation k x ∈
      (Ideal.span {(3 : ℤ_[3]) ^ k} : Ideal ℤ_[3]) := by
    rw [← kernel_three k, RingHom.mem_ker, map_sub, padicResidueApproximation,
      map_natCast, ZMod.natCast_zmod_val, sub_self]
  have hn := (norm_span_three _ k).mpr hi
  rw [dist_eq_norm, norm_sub_rev]
  convert hn using 1
  simp [zpow_neg, zpow_natCast, one_div, inv_pow]

theorem padic_residue_approximation_tendsto (x : ℤ_[3]) :
    Tendsto (fun k => padicResidueApproximation k x) atTop (𝓝 x) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => padic_residue_approximation_bound k x)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem padic_cylinders_generate_borel :
    borel ℤ_[3] = MeasurableSpace.generateFrom padicCylinders := by
  let σ := MeasurableSpace.generateFrom padicCylinders
  have hm (k : ℕ) : @Measurable ℤ_[3] ℤ_[3] σ padicThreeMeasurableSpace
      (padicResidueApproximation k) := by
    letI : MeasurableSpace (ZMod (3 ^ k)) := ⊤
    letI : MeasurableSingletonClass (ZMod (3 ^ k)) := ⟨fun _ => trivial⟩
    have hp : @Measurable ℤ_[3] (ZMod (3 ^ k)) σ ⊤ (PadicInt.toZModPow k) := by
      apply @measurable_to_countable (ZMod (3 ^ k)) ℤ_[3] ⊤ _ σ
      intro x
      exact MeasurableSpace.measurableSet_generateFrom ⟨k, PadicInt.toZModPow k x, rfl⟩
    have hg : @Measurable (ZMod (3 ^ k)) ℤ_[3] ⊤ padicThreeMeasurableSpace
        (fun v => (v.val : ℤ_[3])) :=
      @measurable_of_countable (ZMod (3 ^ k)) ℤ_[3] ⊤ padicThreeMeasurableSpace _ _ _
    exact hg.comp hp
  have hid : @Measurable ℤ_[3] ℤ_[3] σ padicThreeMeasurableSpace id := by
    apply @measurable_of_tendsto_metrizable ℤ_[3] ℤ_[3] σ _ _
      padicThreeMeasurableSpace padicThreeBorelSpace _ _ hm
    exact tendsto_pi_nhds.mpr padic_residue_approximation_tendsto
  apply le_antisymm
  · intro s hs
    exact hid hs
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨k, v, rfl⟩
    exact padic_cylinder_measurable k v

/-- Probability measures on the 3-adic integers are determined by their
residue-cylinder probabilities. -/
theorem padic_probability_eq_of_cylinders (μ ν : Measure ℤ_[3])
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ (k : ℕ) (v : ZMod (3 ^ k)),
      μ {x | PadicInt.toZModPow k x = v} = ν {x | PadicInt.toZModPow k x = v}) : μ = ν := by
  apply ext_of_generate_finite padicCylinders padic_cylinders_generate_borel
    padic_cylinders_piSystem
  · rintro s ⟨k, v, rfl⟩
    exact h k v
  · simp

#print axioms padic_cylinders_piSystem
#print axioms padic_cylinders_generate_borel
#print axioms padic_probability_eq_of_cylinders

end CollatzCylinderPacking.Arithmetic
