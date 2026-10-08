import CanonicalEnvelopeStepMean
import PeriodicMarkedFirstHitMeanFromSources
import EnvelopeOddSuperharmonicLayer

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
open Erdos1135.Tao CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalOddStep_firstHit_mean_nonperiodic {n : ℕ}
    (hn : 0 < n) (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n) (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun K : ℕ => markedFirstHitPartialSum K n (canonicalOddStep j) / (K : ℝ))
      atTop (𝓝 (actualDensityValue actualFirstHitDensity n *
        ∫ x, (canonicalIntegerStep j x).toReal ∂padicThreeHaar)) := by
  obtain ⟨B, hB, hbound⟩ := canonicalOddStep_bounded j
  have h := periodic_marked_firstHit_mean_nonperiodic hn hnp (by positivity : 0 < 2 * 3 ^ j)
    (canonicalOddStep j) (canonicalOddStep_periodic j) hB
    (canonicalOddStep_nonneg j) hbound (fun q hq =>
      canonicalOddStep_zero_of_not_oddUnit j hj q (by tauto))
  rw [canonicalOddStep_mean] at h
  convert h using 1
  congr 1
  ring

theorem canonicalIntegerEnvelope_natCast_eq_of_marked_bound {n : ℕ}
    (hn : 0 < n) (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n)
    (hbound : ∀ j K : ℕ, 1 ≤ j →
      markedFirstHitPartialSum K n (canonicalOddStep j) ≤
        ((K : ℝ) + 1) * (canonicalIntegerEnvelope (n : ℤ_[3])).toReal) :
    canonicalIntegerEnvelope (n : ℤ_[3]) = actualIntegerTrace n := by
  have hupper : Tendsto
      (fun K : ℕ => (((K : ℝ) + 1) * (canonicalIntegerEnvelope (n : ℤ_[3])).toReal) / K)
      atTop (𝓝 (canonicalIntegerEnvelope (n : ℤ_[3])).toReal) := by
    have h := (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).mul_const (canonicalIntegerEnvelope (n : ℤ_[3])).toReal
    simpa only [one_mul, zero_add, div_one, add_comm, add_zero, div_mul_eq_mul_div] using h
  have hstep (j : ℕ) :
      actualDensityValue actualFirstHitDensity n *
        (∫ x, (canonicalIntegerStep (j + 1) x).toReal ∂padicThreeHaar) ≤
      (canonicalIntegerEnvelope (n : ℤ_[3])).toReal := by
    apply le_of_tendsto_of_tendsto
      (canonicalOddStep_firstHit_mean_nonperiodic hn hnp (j + 1) (by omega)) hupper
    exact Eventually.of_forall fun K => div_le_div_of_nonneg_right
      (hbound (j + 1) K (by omega)) (Nat.cast_nonneg K)
  have hlim : Tendsto (fun j => actualDensityValue actualFirstHitDensity n *
      (∫ x, (canonicalIntegerStep (j + 1) x).toReal ∂padicThreeHaar)) atTop
      (𝓝 (actualDensityValue actualFirstHitDensity n)) := by
    simpa only [Function.comp_def, mul_one] using
      (canonicalIntegerStep_integral_tendsto_one.comp (tendsto_add_atTop_nat 1)).const_mul
        (actualDensityValue actualFirstHitDensity n)
  have hle := le_of_tendsto hlim (Eventually.of_forall hstep)
  apply le_antisymm (canonicalIntegerEnvelope_natCast_le n hn)
  change ENNReal.ofReal (actualDensityValue actualFirstHitDensity n) ≤ _
  rw [ENNReal.ofReal_le_iff_le_toReal
    (ne_of_lt ((canonicalIntegerEnvelope_natCast_le n hn).trans_lt (actualIntegerTrace_lt_top n)))]
  exact hle

#print axioms canonicalIntegerEnvelope_natCast_eq_of_marked_bound

theorem canonicalIntegerEnvelope_natCast_eq_of_nonperiodic {n : ℕ}
    (hn : 0 < n) (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n) :
    canonicalIntegerEnvelope (n : ℤ_[3]) = actualIntegerTrace n := by
  apply canonicalIntegerEnvelope_natCast_eq_of_marked_bound hn hnp
  intro j K _hj
  obtain ⟨B, _hB, hbound⟩ := canonicalOddStep_bounded j
  exact firstHitPartial_marked_le_integerEnvelope (canonicalOddStep_nonneg j) hbound
    (canonicalOddStep_le_envelope j) K hn

#print axioms canonicalIntegerEnvelope_natCast_eq_of_nonperiodic

end CollatzCanonical.IntegerStationaryEnvelope
