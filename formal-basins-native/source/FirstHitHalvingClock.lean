import FirstHitClockDensity
import FirstHitWeightTransport

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.ClockSqueeze

namespace CollatzCylinderPacking.Arithmetic

theorem shortcut_hit_halving_iff {N q : ℕ} (hne : 2 * q ≠ N) :
    (∃ A, iterate A (2 * q) = N) ↔ ∃ A, iterate A q = N := by
  have h := hit_iff_suffix_of_prefix_avoids (A := 1) (q := 2 * q) (N := N) (by
    intro i hi
    have hi0 : i = 0 := by omega
    simpa only [hi0, iterate] using hne)
  simpa [iterate, step_two_mul] using h

/-- An initial halving leaves the first-hit odd count unchanged, except
when its starting value is already the target. -/
theorem firstHitOddDepth_halving {N q : ℕ} (hne : 2 * q ≠ N) :
    firstHitOddDepth N (2 * q) = firstHitOddDepth N q := by
  classical
  by_cases hh : ∃ A, iterate A q = N
  · have hf := firstHitTime_spec hh
    have hpre : FirstHit (2 * q) N (1 + firstHitTime hh) :=
      firstHit_prepend (by
        intro i hi
        have hi0 : i = 0 := by omega
        simpa only [hi0, iterate] using hne)
        (by simpa [iterate, step_two_mul] using hf)
    rw [firstHitOddDepth_of_first_hit hpre, firstHitOddDepth_of_first_hit hf, oddCount_add]
    simp [oddCount, iterate, step_two_mul]
  · have htwo : ¬∃ A, iterate A (2 * q) = N := fun h => hh ((shortcut_hit_halving_iff hne).mp h)
    simp only [firstHitOddDepth, dif_neg hh, dif_neg htwo]

/-- For every fixed positive tolerance, a sufficiently large initial
halving can only create an exception at the smaller tolerance. The possible
target at the initial even state is among the discarded finite starts. -/
theorem firstHitOddDepth_clock_halving_eventually (N : ℕ) {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
        (firstHitOddDepth N) lam ε (2 * q) ≤
      clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
        (firstHitOddDepth N) lam (ε / 2) q := by
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop N,
    hlog.eventually_ge_atTop (2 * Real.log 2 / ε)] with q hq hlarge
  have hqpos : 0 < q := by omega
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hne : 2 * q ≠ N := by omega
  have hlog0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqpos)
  have htwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogmul : Real.log (2 * q : ℕ) = Real.log 2 + Real.log (q : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hqreal.ne']
  have hbudget : Real.log 2 ≤ (ε / 2) * Real.log (q : ℝ) := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have hlow : (1 - ε) * Real.log (2 * q : ℕ) ≤
      (1 - ε / 2) * Real.log (q : ℝ) := by
    rw [hlogmul]
    nlinarith [mul_nonneg hε.le htwo]
  have hupp : (1 + ε / 2) * Real.log (q : ℝ) ≤
      (1 + ε) * Real.log (2 * q : ℕ) := by
    rw [hlogmul]
    nlinarith [mul_nonneg hε.le hlog0, mul_nonneg hε.le htwo]
  classical
  by_cases hbad : (∃ A, iterate A q = N) ∧
      ¬ ((1 - ε / 2) * Real.log (q : ℝ) / lam ≤ (firstHitOddDepth N q : ℝ) ∧
        (firstHitOddDepth N q : ℝ) ≤ (1 + ε / 2) * Real.log (q : ℝ) / lam)
  · have hr : clockExceptionIndicator (fun q => ∃ A, iterate A q = N)
        (firstHitOddDepth N) lam (ε / 2) q = 1 := by
      simp only [clockExceptionIndicator, if_pos hbad]
    rw [hr]
    exact clockExceptionIndicator_le_one _ _ _ _ _
  · have hgood : ¬ ((∃ A, iterate A (2 * q) = N) ∧
        ¬ ((1 - ε) * Real.log (2 * q : ℕ) / lam ≤ (firstHitOddDepth N (2 * q) : ℝ) ∧
          (firstHitOddDepth N (2 * q) : ℝ) ≤ (1 + ε) * Real.log (2 * q : ℕ) / lam)) := by
      rintro ⟨hh, hn⟩
      have hhq := (shortcut_hit_halving_iff hne).mp hh
      have hg := not_not.mp (fun h => hbad ⟨hhq, h⟩)
      apply hn
      rw [firstHitOddDepth_halving hne]
      exact ⟨(div_le_div_of_nonneg_right hlow hlam.le).trans hg.1,
        hg.2.trans (div_le_div_of_nonneg_right hupp hlam.le)⟩
    simp only [clockExceptionIndicator, if_neg hbad, if_neg hgood, le_refl]

theorem clockExceptionIndicator_antitone_tolerance
    (P : ℕ → Prop) (d : ℕ → ℕ) {lam ε η : ℝ}
    (hlam : 0 ≤ lam) (hεη : ε ≤ η) (q : ℕ) :
    clockExceptionIndicator P d lam η q ≤ clockExceptionIndicator P d lam ε q := by
  have hlog : 0 ≤ Real.log (q : ℝ) := by
    cases q with
    | zero => simp
    | succ q => exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q))
  have hc := div_nonneg hlog hlam
  have hlow : (1 - η) * Real.log (q : ℝ) / lam ≤
      (1 - ε) * Real.log (q : ℝ) / lam := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hc
  have hupp : (1 + ε) * Real.log (q : ℝ) / lam ≤
      (1 + η) * Real.log (q : ℝ) / lam := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hc
  classical
  by_cases hbad : P q ∧ ¬ ((1 - ε) * Real.log (q : ℝ) / lam ≤ (d q : ℝ) ∧
      (d q : ℝ) ≤ (1 + ε) * Real.log (q : ℝ) / lam)
  · have hr : clockExceptionIndicator P d lam ε q = 1 := by
      simp only [clockExceptionIndicator, if_pos hbad]
    rw [hr]
    exact clockExceptionIndicator_le_one _ _ _ _ _
  · have hg : ¬ (P q ∧ ¬ ((1 - η) * Real.log (q : ℝ) / lam ≤ (d q : ℝ) ∧
        (d q : ℝ) ≤ (1 + η) * Real.log (q : ℝ) / lam)) := by
      rintro ⟨hp, hn⟩
      have he := not_not.mp (fun h => hbad ⟨hp, h⟩)
      exact hn ⟨hlow.trans he.1, he.2.trans hupp⟩
    simp only [clockExceptionIndicator, if_neg hbad, if_neg hg, le_refl]

end CollatzCylinderPacking.Arithmetic

#print axioms CollatzCylinderPacking.Arithmetic.shortcut_hit_halving_iff
#print axioms CollatzCylinderPacking.Arithmetic.firstHitOddDepth_halving
#print axioms CollatzCylinderPacking.Arithmetic.firstHitOddDepth_clock_halving_eventually
#print axioms CollatzCylinderPacking.Arithmetic.clockExceptionIndicator_antitone_tolerance
