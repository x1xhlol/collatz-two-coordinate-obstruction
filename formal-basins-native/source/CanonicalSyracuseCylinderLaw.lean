import SyracuseVariableMeasurable
import OptimalFiniteCylinderRate

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace CollatzCylinderPacking.Arithmetic

theorem sequence_residue_probability (k : ℕ) (v : ZMod (3 ^ k)) :
    geometricSequenceMeasure {f : ℕ → ℕ | v = wordResidue k (sequenceWord k f)} =
      ENNReal.ofReal (residueMass k v) := by
  classical
  let s : Set (GeometricWord k) := {w | v = wordResidue k w}
  have h := tsum_measure_preimage_singleton (μ := geometricSequenceMeasure)
    (Set.to_countable s) (f := sequenceWord k)
    (fun w _ => sequenceWord_event_measurable k w)
  change geometricSequenceMeasure (sequenceWord k ⁻¹' s) = _
  rw [← h]
  calc
    (∑' w : s, geometricSequenceMeasure (sequenceWord k ⁻¹' {↑w})) =
        ∑' w : s, ENNReal.ofReal ((1 / 2 : ℝ) ^ wordLength k w) := by
      apply tsum_congr
      intro w
      exact sequenceWord_probability k w
    _ = ∑' w : GeometricWord k,
        s.indicator (fun w => ENNReal.ofReal ((1 / 2 : ℝ) ^ wordLength k w)) w :=
      tsum_subtype s (fun w : GeometricWord k => ENNReal.ofReal ((1 / 2 : ℝ) ^ wordLength k w))
    _ = ∑' w : GeometricWord k, ENNReal.ofReal (residueTerm k v w) := by
      apply tsum_congr
      intro w
      by_cases hw : v = wordResidue k w
      · simp [s, residueTerm, hw]
      · simp [s, residueTerm, hw]
    _ = ENNReal.ofReal (residueMass k v) :=
      (ENNReal.ofReal_tsum_of_nonneg (residueTerm_nonneg k v) (residueTerm_summable k v)).symm

/-- The actual probability measure on the 3-adic integers obtained from
independent geometric exponents and their compatible Syracuse residues. -/
noncomputable def canonicalSyracuseMeasure : Measure ℤ_[3] :=
  geometricSequenceMeasure.map canonicalSyracuseVariable

instance canonicalSyracuseProbability : IsProbabilityMeasure canonicalSyracuseMeasure :=
  geometricSequenceMeasure.isProbabilityMeasure_map canonical_variable_measurable.aemeasurable

theorem canonical_cylinder_probability (k : ℕ) (v : ZMod (3 ^ k)) :
    canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v} =
      ENNReal.ofReal (residueMass k v) := by
  rw [canonicalSyracuseMeasure, Measure.map_apply canonical_variable_measurable
    (padic_cylinder_measurable k v)]
  change geometricSequenceMeasure {f : ℕ → ℕ |
    PadicInt.toZModPow k (canonicalSyracuseVariable f) = v} = _
  simp_rw [canonical_variable_projection]
  simpa only [eq_comm] using sequence_residue_probability k v

theorem canonical_cylinder_real (k : ℕ) (v : ZMod (3 ^ k)) :
    (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal =
      residueMass k v := by
  rw [canonical_cylinder_probability, ENNReal.toReal_ofReal (residue_mass_nonneg k v)]

/-- Equality with the full arithmetic inverse-word law at positive targets. -/
theorem canonical_cylinder_arithmetic {k N : ℕ} (hN : 0 < N) :
    (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = (N : ZMod (3 ^ k))}).toReal =
      arithmeticMass k N := by
  rw [canonical_cylinder_real, arithmetic_mass_eq_residueMass hN]

noncomputable def canonicalMaximumCylinder (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun v : ZMod (3 ^ k) =>
      (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = v}).toReal)

theorem canonical_maximum_eq (k : ℕ) : canonicalMaximumCylinder k = maximumResidueMass k := by
  simp only [canonicalMaximumCylinder, maximumResidueMass, canonical_cylinder_real]

theorem canonical_maximum_bounds {k : ℕ} (hk : 0 < k) :
    (1 / 2 : ℝ) ^ k ≤ canonicalMaximumCylinder k ∧
      canonicalMaximumCylinder k ≤ (2 * (k : ℝ) + 3) / (2 : ℝ) ^ k := by
  rw [canonical_maximum_eq]
  exact maximum_residue_mass_bounds hk

theorem canonical_maximum_exponent :
    Tendsto (fun k : ℕ => -Real.log (canonicalMaximumCylinder k) / ((k : ℝ) * Real.log 3))
      atTop (𝓝 (Real.log 2 / Real.log 3)) := by
  simpa only [canonical_maximum_eq] using maximum_residue_base_three_rate

#print axioms sequence_residue_probability
#print axioms canonical_cylinder_probability
#print axioms canonical_cylinder_arithmetic
#print axioms canonical_maximum_bounds
#print axioms canonical_maximum_exponent

end CollatzCylinderPacking.Arithmetic
