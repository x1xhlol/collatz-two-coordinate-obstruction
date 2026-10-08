import CanonicalEnvelopeStationary

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
open Erdos1135.Tao CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalIntegerStep_integral_eq_toReal (k : ℕ) :
    (∫ x, (canonicalIntegerStep k x).toReal ∂padicThreeHaar) =
      (∫⁻ x, canonicalIntegerStep k x ∂padicThreeHaar).toReal := by
  have h := ofReal_integral_eq_lintegral_ofReal (canonicalIntegerStep_toReal_integrable k)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  simp only [ENNReal.ofReal_toReal (ne_of_lt (canonicalIntegerStep_lt_top k _))] at h
  have h0 : 0 ≤ ∫ x, (canonicalIntegerStep k x).toReal ∂padicThreeHaar :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  exact (ENNReal.toReal_ofReal h0).symm.trans (congrArg ENNReal.toReal h)

theorem canonicalIntegerStep_integral_tendsto_one :
    Tendsto (fun k => ∫ x, (canonicalIntegerStep k x).toReal ∂padicThreeHaar)
      atTop (𝓝 1) := by
  have hmono : Monotone (fun k => ∫⁻ x, canonicalIntegerStep k x ∂padicThreeHaar) := by
    intro k j hkj
    exact lintegral_mono fun x => padicIntegerStep_monotone actualIntegerTrace x hkj
  have hs : (⨆ k, ∫⁻ x, canonicalIntegerStep k x ∂padicThreeHaar) = 1 := by
    change (⨆ k, ∫⁻ x, padicIntegerStep actualIntegerTrace k x ∂padicThreeHaar) = 1
    rw [← padicIntegerEnvelope_lintegral]
    exact canonicalIntegerEnvelope_lintegral_eq_one
  have ht := tendsto_atTop_iSup hmono
  rw [hs] at ht
  have hr := (ENNReal.tendsto_toReal (by finiteness : (1 : ℝ≥0∞) ≠ ⊤)).comp ht
  simpa only [Function.comp_def, ← canonicalIntegerStep_integral_eq_toReal,
    ENNReal.toReal_one] using hr

noncomputable def canonicalOddStep (k q : ℕ) : ℝ :=
  if q % 2 = 1 then (canonicalIntegerStep k (q : ℤ_[3])).toReal else 0

theorem canonicalOddStep_periodic (k : ℕ) :
    Function.Periodic (canonicalOddStep k) (2 * 3 ^ k) := by
  intro q
  have hm : (q + 2 * 3 ^ k) % 2 = q % 2 := by omega
  have he : PadicInt.toZModPow k ((q + 2 * 3 ^ k : ℕ) : ℤ_[3]) =
      PadicInt.toZModPow k (q : ℤ_[3]) := by
    simp only [map_natCast]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
      mul_zero, add_zero]
  simp only [canonicalOddStep, hm, canonicalIntegerStep,
    padicIntegerStep_eq_of_projection_eq actualIntegerTrace k he]

theorem canonicalOddStep_nonneg (k q : ℕ) : 0 ≤ canonicalOddStep k q := by
  unfold canonicalOddStep
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem canonicalOddStep_bounded (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q, canonicalOddStep k q ≤ B := by
  refine ⟨∑ q ∈ Finset.range (2 * 3 ^ k), canonicalOddStep k q,
    Finset.sum_nonneg (fun q _ => canonicalOddStep_nonneg k q), ?_⟩
  intro q
  rw [← (canonicalOddStep_periodic k).map_mod_nat q]
  exact Finset.single_le_sum (fun j _ => canonicalOddStep_nonneg k j)
    (Finset.mem_range.mpr (Nat.mod_lt q (by positivity)))

theorem canonicalOddStep_le_envelope (k q : ℕ) (hq : 0 < q) :
    canonicalOddStep k q ≤ (canonicalIntegerEnvelope (q : ℤ_[3])).toReal := by
  unfold canonicalOddStep
  split_ifs
  · apply ENNReal.toReal_mono
    · exact ne_of_lt ((canonicalIntegerEnvelope_natCast_le q hq).trans_lt
        (actualIntegerTrace_lt_top q))
    · exact padicIntegerStep_le_envelope actualIntegerTrace k _
  · exact ENNReal.toReal_nonneg

theorem canonicalOddStep_zero_of_not_oddUnit (k : ℕ) (hk : 1 ≤ k) (q : ℕ)
    (hq : q % 2 ≠ 1 ∨ q % 3 = 0) : canonicalOddStep k q = 0 := by
  unfold canonicalOddStep
  split_ifs with ho
  · rw [canonicalIntegerStep_zero_of_not_isUnit k hk _
      (by rw [padic_natCast_isUnit_iff]; exact not_not.mpr (hq.resolve_left (not_not.mpr ho))),
      ENNReal.toReal_zero]
  · rfl

theorem canonicalOddStep_mean (k : ℕ) :
    (∑ q ∈ Finset.range (2 * 3 ^ k), canonicalOddStep k q) / (2 * 3 ^ k : ℕ) =
      (1 / 2 : ℝ) * ∫ x, (canonicalIntegerStep k x).toReal ∂padicThreeHaar := by
  let f : ZMod (3 ^ k) → ℝ := fun z => (canonicalIntegerStep k (z.val : ℤ_[3])).toReal
  have he (q : ℕ) : f (q : ZMod (3 ^ k)) = (canonicalIntegerStep k (q : ℤ_[3])).toReal := by
    have h := canonicalIntegerStep_residue k (q : ℤ_[3])
    rw [map_natCast] at h
    exact congrArg ENNReal.toReal h
  have heq : (fun x => f (PadicInt.toZModPow k x)) =
      (fun x => (canonicalIntegerStep k x).toReal) := by
    funext x
    exact congrArg ENNReal.toReal (canonicalIntegerStep_residue k x)
  rw [← heq, integral_padicThreeHaar_cylinder]
  have hs := odd_mask_cylinder_sum k f
  simp only [he] at hs
  change (∑ q ∈ Finset.range (2 * 3 ^ k),
    if q % 2 = 1 then (canonicalIntegerStep k (q : ℤ_[3])).toReal else 0) /
      (2 * 3 ^ k : ℕ) = _
  rw [hs]
  push_cast
  ring

#print axioms canonicalIntegerStep_integral_tendsto_one
#print axioms canonicalOddStep_mean

end CollatzCanonical.IntegerStationaryEnvelope
