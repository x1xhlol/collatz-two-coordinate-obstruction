import FirstHitClockConversion
import LogarithmicFinitePerturbation

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze

namespace CollatzCylinderPacking.Arithmetic

noncomputable def firstHitElapsed (N q : ℕ) : ℕ := by
  classical
  exact if hh : ∃ A, iterate A q = N then firstHitTime hh else 0

theorem firstHitElapsed_eq {N q : ℕ} (hh : ∃ A, iterate A q = N) :
    firstHitElapsed N q = firstHitTime hh := by
  simp [firstHitElapsed, hh]

theorem clockExceptionIndicator_le_one (P : ℕ → Prop) (d : ℕ → ℕ)
    (lam ε : ℝ) (q : ℕ) : clockExceptionIndicator P d lam ε q ≤ 1 := by
  unfold clockExceptionIndicator
  split_ifs <;> norm_num

/-- The checked deterministic first-hit identity transfers a zero logarithmic
exceptional-set law from odd-step counts to elapsed shortcut time. -/
theorem first_hit_elapsed_clock_exception_mean {N : ℕ} (hN : 0 < N)
    (P : ℕ → Prop) (hP : ∀ q, P q → ∃ A, iterate A q = N)
    (hE : ∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative
        (clockExceptionIndicator P (firstHitOddDepth N) (Real.log (4 / 3 : ℝ)) η) t / t)
        atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator P (firstHitElapsed N) (Real.log (4 / 3 : ℝ) / 2) ε) t / t)
      atTop (𝓝 0) := by
  let lam := Real.log (4 / 3 : ℝ)
  have hlam : 0 < lam := Real.log_pos (by norm_num)
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hthree : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ Real.log (3 : ℝ) / Real.log 2 := (div_pos hthree htwo).le
  have hA2 : Real.log (3 : ℝ) / Real.log 2 ≤ 2 := by
    apply (div_le_iff₀ htwo).mpr
    have hx := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
    have hy : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith
  obtain ⟨C, hC0, hbound⟩ := first_hit_clock_conversion hN
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply zero_logarithmic_mean_of_eventual_le
    (fun q => ⟨clockExceptionIndicator_nonneg _ _ _ _ q,
      clockExceptionIndicator_le_one _ _ _ _ q⟩)
    (fun q => clockExceptionIndicator_nonneg P (firstHitOddDepth N) lam (ε / 2) q) _
    (hE (ε / 2) (by positivity) (by linarith))
  filter_upwards [hlog.eventually (eventually_ge_atTop (C * lam / ε)),
    eventually_ge_atTop (1 : ℕ)] with q hlarge hq
  have hlog0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hC : C ≤ ε * Real.log (q : ℝ) / lam := by
    apply (le_div_iff₀ hlam).mpr
    have hx := (div_le_iff₀ hε).mp hlarge
    nlinarith
  classical
  by_cases hp : P q
  · by_cases hg : (1 - ε / 2) * Real.log (q : ℝ) / lam ≤ (firstHitOddDepth N q : ℝ) ∧
        (firstHitOddDepth N q : ℝ) ≤ (1 + ε / 2) * Real.log (q : ℝ) / lam
    · have hodd : |(firstHitOddDepth N q : ℝ) - Real.log (q : ℝ) / lam| ≤
          (ε / 2) * Real.log (q : ℝ) / lam := by
        apply abs_le.mpr
        have hlo : (1 - ε / 2) * Real.log (q : ℝ) / lam = Real.log (q : ℝ) / lam - (ε / 2) * Real.log (q : ℝ) / lam := by ring
        have hhi : (1 + ε / 2) * Real.log (q : ℝ) / lam = Real.log (q : ℝ) / lam + (ε / 2) * Real.log (q : ℝ) / lam := by ring
        rw [hlo, hhi] at hg
        constructor <;> linarith [hg.1, hg.2]
      have hh := hP q hp
      have hb := hbound q hh
      rw [← firstHitElapsed_eq hh] at hb
      have hmul := mul_le_mul_of_nonneg_left hodd hA0
      have hcoef := mul_le_mul_of_nonneg_right hA2
        (show 0 ≤ (ε / 2) * Real.log (q : ℝ) / lam by positivity)
      have he : |(firstHitElapsed N q : ℝ) - 2 * Real.log (q : ℝ) / lam| ≤
          2 * ε * Real.log (q : ℝ) / lam := by
        change |(firstHitElapsed N q : ℝ) - 2 * Real.log (q : ℝ) / lam| ≤
          (Real.log 3 / Real.log 2) * |(firstHitOddDepth N q : ℝ) - Real.log (q : ℝ) / lam| + C at hb
        calc
          _ ≤ _ := hb
          _ ≤ 2 * ((ε / 2) * Real.log (q : ℝ) / lam) + ε * Real.log (q : ℝ) / lam :=
            add_le_add (hmul.trans hcoef) hC
          _ = _ := by ring
      have hed := abs_le.mp he
      have ht : (1 - ε) * Real.log (q : ℝ) / (lam / 2) ≤ (firstHitElapsed N q : ℝ) ∧
          (firstHitElapsed N q : ℝ) ≤ (1 + ε) * Real.log (q : ℝ) / (lam / 2) := by
        constructor <;> dsimp <;> field_simp at * <;> nlinarith
      change clockExceptionIndicator P (firstHitElapsed N) (lam / 2) ε q ≤
        clockExceptionIndicator P (firstHitOddDepth N) lam (ε / 2) q
      simp [clockExceptionIndicator, hp, ht, hg]
    · have hv : clockExceptionIndicator P (firstHitOddDepth N) lam (ε / 2) q = 1 := by
        simp [clockExceptionIndicator, hp, hg]
      rw [hv]
      exact clockExceptionIndicator_le_one _ _ _ _ q
  · simp [clockExceptionIndicator, hp]

end CollatzCylinderPacking.Arithmetic
