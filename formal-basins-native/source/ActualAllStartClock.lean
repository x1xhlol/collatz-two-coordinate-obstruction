import DyadicFamilyMean
import FirstHitHalvingClock
import NativeActualClockException

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze
open CollatzCanonical.GreenKernelScalars CollatzCanonical.NativeTao

namespace CollatzCylinderPacking.Arithmetic

theorem oddRestriction_clockExceptionIndicator (P : ℕ → Prop) (d : ℕ → ℕ)
    (lam ε : ℝ) :
    CollatzCanonical.Halving.oddRestriction (clockExceptionIndicator P d lam ε) =
      clockExceptionIndicator (fun q => q % 2 = 1 ∧ P q) d lam ε := by
  funext q
  classical
  by_cases ho : q % 2 = 1 <;>
    simp [CollatzCanonical.Halving.oddRestriction, clockExceptionIndicator, ho]

/-- The actual first-hit odd-source count has an absolute zero-density
exceptional set among all positive starts, including every initial halving
class and every positive target. -/
theorem actual_all_start_firstHitOddDepth_exception_mean_zero (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
        (firstHitOddDepth N) (2 * delta) ε) t / t) atTop (𝓝 0) := by
  apply CollatzCanonical.Halving.logarithmic_family_mean_zero_of_halving
    (fun e => clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
      (firstHitOddDepth N) (2 * delta) e)
  · intro e _ q
    exact ⟨clockExceptionIndicator_nonneg _ _ _ _ _, clockExceptionIndicator_le_one _ _ _ _ _⟩
  · intro e he
    rw [oddRestriction_clockExceptionIndicator]
    exact actual_firstHitOddDepth_exception_mean_zero N he
  · intro e he
    exact firstHitOddDepth_clock_halving_eventually N (mul_pos (by norm_num) delta_pos) he
  · exact hε

/-- On all positive starts in a fixed actual basin, elapsed shortcut time
has center `2 * log q / log(4/3)` and an absolute zero logarithmic-density
exceptional set at every positive relative tolerance. -/
theorem actual_all_start_firstHitElapsed_exception_mean_zero {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
        (firstHitElapsed N) (Real.log (4 / 3 : ℝ) / 2) ε) t / t)
      atTop (𝓝 0) := by
  let η : ℝ := min ε (1 / 2)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hlim : Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
        (firstHitElapsed N) (Real.log (4 / 3 : ℝ) / 2) η) t / t)
      atTop (𝓝 0) := by
    apply first_hit_elapsed_clock_exception_mean hN
      (fun q => ∃ A, iterate A q = N) (fun _ h => h) _ hη hη1
    intro e he _
    have h := actual_all_start_firstHitOddDepth_exception_mean_zero N he
    have hd : 2 * delta = Real.log (4 / 3 : ℝ) := by unfold delta; ring
    simpa only [hd] using h
  apply zero_logarithmic_mean_of_eventual_le
    (fun q => ⟨clockExceptionIndicator_nonneg _ _ _ _ _, clockExceptionIndicator_le_one _ _ _ _ _⟩)
    (fun q => clockExceptionIndicator_nonneg _ _ _ _ _) _ hlim
  apply Eventually.of_forall
  intro q
  exact clockExceptionIndicator_antitone_tolerance _ _
    (div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4 / 3)) (by norm_num)) hηε q

end CollatzCylinderPacking.Arithmetic

#print axioms CollatzCylinderPacking.Arithmetic.oddRestriction_clockExceptionIndicator
#print axioms CollatzCylinderPacking.Arithmetic.actual_all_start_firstHitOddDepth_exception_mean_zero
#print axioms CollatzCylinderPacking.Arithmetic.actual_all_start_firstHitElapsed_exception_mean_zero
