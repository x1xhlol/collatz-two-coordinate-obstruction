import ActualClockAdapter
import ActualInverseOperator
import UniformOrbitCorrection

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem positive_of_hit_positive {q N A : ℕ} (hN : 0 < N) (hhit : iterate A q = N) :
    0 < q := by
  by_contra hq
  have hz : q = 0 := by omega
  rw [hz, iterate_zero] at hhit
  omega

/-- A first-hit path has no repeated state, including its final target. -/
theorem first_hit_path_injective {q N A : ℕ} (hfirst : FirstHit q N A) :
    Set.InjOn (fun i => iterate i q) (Finset.range (A + 1)) := by
  have hstrict (i j : ℕ) (hj : j ≤ A) (hij : i < j)
      (he : iterate i q = iterate j q) : False := by
    have htime : j + (A - j) = A := by omega
    have hhit : iterate (i + (A - j)) q = N := by
      rw [iterate_add, he, ← iterate_add, htime, hfirst.1]
    exact hfirst.2 (i + (A - j)) (by omega) hhit
  intro i hi j hj he
  have hi' : i ≤ A := by simpa using hi
  have hj' : j ≤ A := by simpa using hj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hstrict i j hj' hij he)
  · exact hij
  · exact False.elim (hstrict j i hi' hij he.symm)

/-- A single bound controls the actual correction products of all first hits. -/
theorem exists_uniform_first_hit_correction_bound :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ (q N A : ℕ), 0 < N → FirstHit q N A →
      1 ≤ pathCorrection A q ∧ pathCorrection A q ≤ P₀ := by
  obtain ⟨P₀, hP₀, hb⟩ := CollatzCanonical.UniformCorrection.exists_uniform_finite_path_product_bound
  refine ⟨P₀, hP₀, ?_⟩
  intro q N A hN hfirst
  have hq := positive_of_hit_positive hN hfirst.1
  have hinj : Set.InjOn (fun i => iterate i q) (Finset.range A) :=
    (first_hit_path_injective hfirst).mono (Finset.range_mono (by omega))
  exact hb A (fun i => iterate i q) hq (fun i _ => rfl) hinj

/-- The actual first-hit correction product, with harmless value one off the basin. -/
noncomputable def firstHitCorrectionProduct (N q : ℕ) : ℝ := by
  classical
  exact if hh : ∃ A, iterate A q = N then pathCorrection (firstHitTime hh) q else 1

theorem firstHitCorrectionProduct_of_first_hit {q N A : ℕ} (hfirst : FirstHit q N A) :
    firstHitCorrectionProduct N q = pathCorrection A q := by
  classical
  have hh : ∃ A, iterate A q = N := ⟨A, hfirst.1⟩
  have he := firstHit_time_unique (firstHitTime_spec hh) hfirst
  simp only [firstHitCorrectionProduct, dif_pos hh, he]

theorem exists_uniform_first_hit_log_correction_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (N q : ℕ), 0 < N → (∃ A, iterate A q = N) →
      0 ≤ Real.log (firstHitCorrectionProduct N q) ∧
        Real.log (firstHitCorrectionProduct N q) ≤ L := by
  obtain ⟨P₀, hP₀, hb⟩ := exists_uniform_first_hit_correction_bound
  refine ⟨Real.log P₀, Real.log_nonneg hP₀, ?_⟩
  intro N q hN hh
  have hf := firstHitTime_spec hh
  rw [firstHitCorrectionProduct_of_first_hit hf]
  have hp := hb q N (firstHitTime hh) hN hf
  exact ⟨Real.log_nonneg hp.1, Real.log_le_log (by linarith [hp.1]) hp.2⟩

/-- Exact logarithmic relation between elapsed shortcut time, odd-source
count, endpoint size, and the actual first-hit correction product. -/
theorem first_hit_log_identity {q N A : ℕ} (hN : 0 < N) (hfirst : FirstHit q N A) :
    (A : ℝ) * Real.log 2 = (oddCount A q : ℝ) * Real.log 3 +
      Real.log q - Real.log N + Real.log (firstHitCorrectionProduct N q) := by
  have hq := positive_of_hit_positive hN hfirst.1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hP : pathCorrection A q ≠ 0 := by
    have hp := one_le_pathCorrection A q
    linarith
  have hid := CollatzCanonical.Correction.iterate_correction_identity A hq
  rw [hfirst.1] at hid
  change (2 : ℝ) ^ A * N = (3 : ℝ) ^ oddCount A q * q * pathCorrection A q at hid
  have hl := congrArg Real.log hid
  rw [Real.log_mul (pow_ne_zero A (by norm_num)) hNr,
    Real.log_mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) hqr) hP,
    Real.log_mul (pow_ne_zero _ (by norm_num)) hqr, Real.log_pow, Real.log_pow] at hl
  rw [firstHitCorrectionProduct_of_first_hit hfirst]
  linarith

theorem first_hit_time_log_identity {N q : ℕ} (hN : 0 < N)
    (hhit : ∃ A, iterate A q = N) :
    (firstHitTime hhit : ℝ) * Real.log 2 = (firstHitOddDepth N q : ℝ) * Real.log 3 +
      Real.log q - Real.log N + Real.log (firstHitCorrectionProduct N q) := by
  rw [firstHitOddDepth_of_first_hit (firstHitTime_spec hhit)]
  exact first_hit_log_identity hN (firstHitTime_spec hhit)

theorem clock_log_four_thirds : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [he]

/-- Exact centered-clock relation, prior to applying the uniform product bound. -/
theorem first_hit_centered_clock_identity {N q : ℕ} (hN : 0 < N)
    (hhit : ∃ A, iterate A q = N) :
    (firstHitTime hhit : ℝ) - 2 * Real.log q / Real.log (4 / 3 : ℝ) =
      (Real.log 3 / Real.log 2) *
        ((firstHitOddDepth N q : ℝ) - Real.log q / Real.log (4 / 3 : ℝ)) +
      (Real.log (firstHitCorrectionProduct N q) - Real.log N) / Real.log 2 := by
  have hid := first_hit_time_log_identity hN hhit
  have htwo : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlam : Real.log (4 / 3 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hl := clock_log_four_thirds
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * Real.log (4 / 3 : ℝ)) hid,
    congrArg (fun x : ℝ => x * Real.log q) hl]

/-- For each fixed positive target, shortcut-clock error is bounded by the
odd-clock error plus a constant independent of the starting basin element. -/
theorem first_hit_clock_conversion {N : ℕ} (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (hhit : ∃ A, iterate A q = N),
      |(firstHitTime hhit : ℝ) - 2 * Real.log q / Real.log (4 / 3 : ℝ)| ≤
        (Real.log 3 / Real.log 2) *
          |(firstHitOddDepth N q : ℝ) - Real.log q / Real.log (4 / 3 : ℝ)| + C := by
  obtain ⟨L, hL, hb⟩ := exists_uniform_first_hit_log_correction_bound
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hth : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hNlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  refine ⟨(L + Real.log N) / Real.log 2, by positivity, ?_⟩
  intro q hh
  have hp := hb N q hN hh
  rw [first_hit_centered_clock_identity hN hh]
  calc
    _ ≤ |(Real.log 3 / Real.log 2) *
        ((firstHitOddDepth N q : ℝ) - Real.log q / Real.log (4 / 3 : ℝ))| +
        |(Real.log (firstHitCorrectionProduct N q) - Real.log N) / Real.log 2| := abs_add_le _ _
    _ = (Real.log 3 / Real.log 2) *
        |(firstHitOddDepth N q : ℝ) - Real.log q / Real.log (4 / 3 : ℝ)| +
        |Real.log (firstHitCorrectionProduct N q) - Real.log N| / Real.log 2 := by
      rw [abs_mul, abs_of_pos (div_pos hth ht), abs_div, abs_of_pos ht]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ ht.le
      calc
        |Real.log (firstHitCorrectionProduct N q) - Real.log N| ≤
            |Real.log (firstHitCorrectionProduct N q)| + |Real.log N| := abs_sub _ _
        _ ≤ L + Real.log N := by rw [abs_of_nonneg hp.1, abs_of_nonneg hNlog]; linarith [hp.2]

end CollatzCylinderPacking.Arithmetic
