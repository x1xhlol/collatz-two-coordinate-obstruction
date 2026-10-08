import CanonicalEnvelopeStationary
import CanonicalSyracLawBridge

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal
open Erdos1135.Tao CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonical_cylinder_mass_ge_of_unit_floor {c : ℝ≥0∞}
    (hfloor : ∀ x : ℤ_[3], IsUnit x → c ≤ canonicalIntegerEnvelope x)
    {k : ℕ} (hk : 1 ≤ k) (b : ZMod (3 ^ k)) (hb : b.val % 3 ≠ 0) :
    c * (3 ^ k : ℝ≥0∞)⁻¹ ≤
      canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = b} := by
  let C : Set ℤ_[3] := {x | PadicInt.toZModPow k x = b}
  have hC : MeasurableSet C := padic_cylinder_measurable k b
  have hunit : ∀ x ∈ C, IsUnit x := by
    intro x hx
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    apply (padicThree_isUnit_iff_projection_val_mod_three j x).mpr
    simpa only [show PadicInt.toZModPow (j + 1) x = b from hx] using hb
  change _ ≤ canonicalSyracuseMeasure C
  rw [← canonicalIntegerEnvelope_withDensity, withDensity_apply _ hC]
  calc
    _ = ∫⁻ _ : ℤ_[3] in C, c ∂padicThreeHaar := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact congrArg (fun v => c * v) (padicThreeHaar_cylinder k b).symm
    _ ≤ ∫⁻ x : ℤ_[3] in C, canonicalIntegerEnvelope x ∂padicThreeHaar := by
      apply lintegral_mono_ae
      exact (ae_restrict_iff' hC).mpr (Eventually.of_forall fun x hx => hfloor x (hunit x hx))

theorem canonicalRho_ge_of_unit_floor {c : ℝ≥0∞}
    (hfloor : ∀ x : ℤ_[3], IsUnit x → c ≤ canonicalIntegerEnvelope x)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) (hn : n % 3 ≠ 0) :
    c.toReal ≤ canonicalRho k n := by
  let b : ZMod (3 ^ k) := n
  have hb : b.val % 3 ≠ 0 := by
    have hu := (padic_natCast_isUnit_iff n).mpr hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have h := (padicThree_isUnit_iff_projection_val_mod_three j (n : ℤ_[3])).mp hu
    simpa only [map_natCast] using h
  have hmass := canonical_cylinder_mass_ge_of_unit_floor hfloor hk b hb
  have hreal := ENNReal.toReal_mono (measure_ne_top canonicalSyracuseMeasure _) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at hreal
  change c.toReal ≤ (3 : ℝ) ^ k *
    (canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = b}).toReal
  have hp : 0 < (3 : ℝ) ^ k := by positivity
  have hm := mul_le_mul_of_nonneg_left hreal hp.le
  have he : (3 : ℝ) ^ k * (c.toReal * ((3 : ℝ) ^ k)⁻¹) = c.toReal := by field_simp
  rwa [he] at hm

theorem exists_uniform_canonicalRho_unit_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, n % 3 ≠ 0 →
      c ≤ canonicalRho k n := by
  obtain ⟨c, hc, hcfin, hfloor⟩ := canonicalIntegerEnvelope_uniform_unit_floor
  refine ⟨c.toReal, ENNReal.toReal_pos (ne_of_gt hc) (ne_of_lt hcfin), ?_⟩
  intro k hk n hn
  exact canonicalRho_ge_of_unit_floor hfloor hk n hn

theorem exists_uniform_canonical_cylinder_unit_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ b : ZMod (3 ^ k), b.val % 3 ≠ 0 →
      ENNReal.ofReal c * (3 ^ k : ℝ≥0∞)⁻¹ ≤
        canonicalSyracuseMeasure {x : ℤ_[3] | PadicInt.toZModPow k x = b} := by
  obtain ⟨c, hc, hcfin, hfloor⟩ := canonicalIntegerEnvelope_uniform_unit_floor
  refine ⟨c.toReal, ENNReal.toReal_pos (ne_of_gt hc) (ne_of_lt hcfin), ?_⟩
  intro k hk b hb
  rw [ENNReal.ofReal_toReal (ne_of_lt hcfin)]
  exact canonical_cylinder_mass_ge_of_unit_floor hfloor hk b hb

theorem exists_uniform_syracPMF_unit_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ b : ZMod (3 ^ k), b.val % 3 ≠ 0 →
      ENNReal.ofReal c * (3 ^ k : ℝ≥0∞)⁻¹ ≤ syracPMF k b := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_canonical_cylinder_unit_floor
  refine ⟨c, hc, ?_⟩
  intro k hk b hb
  simpa only [canonical_cylinder_eq_syracPMF] using hfloor k hk b hb

theorem exists_uniform_syracPMF_toReal_unit_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ b : ZMod (3 ^ k), b.val % 3 ≠ 0 →
      c * ((3 : ℝ) ^ k)⁻¹ ≤ (syracPMF k b).toReal := by
  obtain ⟨c, hc, hfloor⟩ := exists_uniform_syracPMF_unit_floor
  refine ⟨c, hc, ?_⟩
  intro k hk b hb
  have h := ENNReal.toReal_mono (PMF.apply_ne_top _ _) (hfloor k hk b hb)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using h

#print axioms exists_uniform_canonicalRho_unit_floor
#print axioms exists_uniform_canonical_cylinder_unit_floor
#print axioms exists_uniform_syracPMF_unit_floor
#print axioms exists_uniform_syracPMF_toReal_unit_floor

end CollatzCanonical.IntegerStationaryEnvelope
