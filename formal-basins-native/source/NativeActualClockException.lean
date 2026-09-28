import NativeTargetClockDensity
import ClockExceptionalDensity
import GreenKernelScalars

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao

open Erdos1135.Tao CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzClockAudit CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze
open CollatzCanonical.GreenKernelScalars

theorem clockDrift_eq_two_delta : clockDrift = 2 * delta := by
  unfold clockDrift delta
  ring

theorem actual_clockExceptionIndicator_eq_event (N : ℕ) (ε : ℝ) (q : ℕ) :
    clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ K, iterate K q = N)
      (firstHitOddDepth N) (2 * delta) ε q =
      oddEventWeight (actualTargetClockBadEvent N ε) q := by
  classical
  have hinterval :
      ((1 - ε) * Real.log (q : ℝ) / (2 * delta) ≤ (firstHitOddDepth N q : ℝ) ∧
        (firstHitOddDepth N q : ℝ) ≤ (1 + ε) * Real.log (q : ℝ) / (2 * delta)) ↔
      |(firstHitOddDepth N q : ℝ) - Real.log (q : ℝ) / clockDrift| ≤
        ε * Real.log (q : ℝ) / clockDrift := by
    rw [← clockDrift_eq_two_delta, abs_le]
    have hl : (1 - ε) * Real.log (q : ℝ) / clockDrift =
        Real.log (q : ℝ) / clockDrift - ε * Real.log (q : ℝ) / clockDrift := by ring
    have hu : (1 + ε) * Real.log (q : ℝ) / clockDrift =
        Real.log (q : ℝ) / clockDrift + ε * Real.log (q : ℝ) / clockDrift := by ring
    rw [hl, hu]
    constructor <;> intro h <;> constructor <;> linarith
  have he :
      ((q % 2 = 1 ∧ ∃ K, iterate K q = N) ∧
        ¬ ((1 - ε) * Real.log (q : ℝ) / (2 * delta) ≤ (firstHitOddDepth N q : ℝ) ∧
          (firstHitOddDepth N q : ℝ) ≤ (1 + ε) * Real.log (q : ℝ) / (2 * delta))) ↔
      ∃ hq : Odd q, (⟨q, hq⟩ : TaoOddNat) ∈ actualTargetClockBadEvent N ε := by
    constructor
    · rintro ⟨⟨ho, hbasin⟩, hbad⟩
      exact ⟨Nat.odd_iff.mpr ho, hbasin, not_le.mp (fun h => hbad (hinterval.mpr h))⟩
    · rintro ⟨ho, hbasin, hbad⟩
      exact ⟨⟨Nat.odd_iff.mp ho, hbasin⟩, fun h => (not_le_of_gt hbad) (hinterval.mp h)⟩
  simp only [clockExceptionIndicator, oddEventWeight, he]

/-- The absolute target-clock exceptional-set hypothesis used by the
canonical trace theorem is discharged for every target and every ε>0. -/
theorem actual_firstHitOddDepth_exception_mean_zero (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ K, iterate K q = N)
        (firstHitOddDepth N) (2 * delta) ε) t / t) atTop (𝓝 0) := by
  classical
  have h := actual_target_clock_exception_logarithmic_mean_zero N hε
  have hw : (fun q => if q % 2 = 1 then
      oddEventWeight (actualTargetClockBadEvent N ε) q else 0) =
      clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ K, iterate K q = N)
        (firstHitOddDepth N) (2 * delta) ε := by
    funext q
    rw [actual_clockExceptionIndicator_eq_event]
    by_cases ho : q % 2 = 1
    · simp only [ho, if_true]
    · have hnot : ¬∃ hq : Odd q,
          (⟨q, hq⟩ : TaoOddNat) ∈ actualTargetClockBadEvent N ε := by
        rintro ⟨hq, _⟩
        exact ho (Nat.odd_iff.mp hq)
      simp only [ho, if_false, oddEventWeight, hnot]
  simpa only [oddLogarithmicCumulative, hw] using h

#print axioms actual_clockExceptionIndicator_eq_event
#print axioms actual_firstHitOddDepth_exception_mean_zero

end CollatzCanonical.NativeTao
