import PeriodicMarkedFirstHitMeanFromSources
import EnvelopeOddSuperharmonicLayer
import FixedBasinGreenBoundary

set_option autoImplicit false

open Filter Topology
open scoped BigOperators
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.GreenKernelScalars

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem layer_actualDensityValue_nonneg (q : ℕ) :
    0 ≤ actualDensityValue actualFirstHitDensity q := by
  cases q with
  | zero => simp [actualDensityValue]
  | succ q =>
    unfold actualDensityValue
    exact mul_nonneg (mul_nonneg (mul_nonneg delta_pos.le
      (greenCycleFactor_one_pos (Nat.succ_pos q)).le) (Nat.cast_nonneg _))
      (actualFirstHitDensity_nonneg _)

private theorem layer_iterate_one_eq_one_or_two (k : ℕ) :
    iterate k 1 = 1 ∨ iterate k 1 = 2 := by
  induction k with
  | zero => simp only [iterate, true_or]
  | succ k ih =>
    rcases ih with h | h <;> simp only [iterate, h, step] <;> norm_num

private theorem layer_five_nonperiodic : ¬ ∃ r : ℕ, 0 < r ∧ iterate r 5 = 5 := by
  rintro ⟨r, hr, hret⟩
  have hfour : iterate 4 5 = 1 := by norm_num [iterate, step]
  have hbig := iterate_mul_period hret 4
  have he : 4 * r = 4 + (4 * r - 4) := by omega
  rw [he, iterate_add, hfour] at hbig
  have hm := layer_iterate_one_eq_one_or_two (4 * r - 4)
  omega

theorem periodic_actual_density_value_mean_le_half_from_layers {M : ℕ}
    (hM : 0 < M) (f : ℕ → ℝ) (hp : Function.Periodic f M) {L : ℝ} (hL : 0 ≤ L)
    (hf0 : ∀ q, 0 ≤ f q) (hfL : ∀ q, f q ≤ L)
    (hsupport : ∀ q, ¬ (q % 2 = 1 ∧ q % 3 ≠ 0) → f q = 0)
    (hdom : ∀ q, 0 < q → q % 3 ≠ 0 →
      f q ≤ actualDensityValue actualFirstHitDensity q) :
    (∑ q ∈ Finset.range M, f q) / (M : ℝ) ≤ 1 / 2 := by
  have hgpos : 0 < actualDensityValue actualFirstHitDensity 5 :=
    (actual_trace_positive_iff_unit (by decide : 0 < 5)).mpr (by decide)
  have hg : BinarySuperharmonic (actualDensityValue actualFirstHitDensity) := by
    intro q hq
    exact (actual_unconditional_density_harmonic hq).ge
  have hdom' (q : ℕ) (hq : 0 < q) : f q ≤ actualDensityValue actualFirstHitDensity q := by
    by_cases hu : q % 3 ≠ 0
    · exact hdom q hq hu
    · rw [hsupport q (fun h => hu h.2)]
      exact layer_actualDensityValue_nonneg q
  have hbound (K : ℕ) : markedFirstHitPartialSum K 5 f ≤
      ((K : ℝ) + 1) * actualDensityValue actualFirstHitDensity 5 :=
    firstHitPartial_marked_le_superharmonic layer_actualDensityValue_nonneg hg
      hf0 hfL hdom' K (by decide)
  have hupper : Tendsto
      (fun K : ℕ => (((K : ℝ) + 1) * actualDensityValue actualFirstHitDensity 5) / K)
      atTop (𝓝 (actualDensityValue actualFirstHitDensity 5)) := by
    have h := (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).mul_const (actualDensityValue actualFirstHitDensity 5)
    simpa only [one_mul, zero_add, div_one, add_comm, add_zero, div_mul_eq_mul_div] using h
  have hmean := periodic_marked_firstHit_mean_nonperiodic (by decide : 0 < 5)
    layer_five_nonperiodic hM f hp hL hf0 hfL hsupport
  have hle : 2 * actualDensityValue actualFirstHitDensity 5 *
      ((∑ q ∈ Finset.range M, f q) / (M : ℝ)) ≤ actualDensityValue actualFirstHitDensity 5 := by
    apply le_of_tendsto_of_tendsto hmean hupper
    exact Eventually.of_forall fun K =>
      div_le_div_of_nonneg_right (hbound K) (Nat.cast_nonneg K)
  nlinarith

#print axioms periodic_actual_density_value_mean_le_half_from_layers

end CollatzCanonical.IntegerStationaryEnvelope
