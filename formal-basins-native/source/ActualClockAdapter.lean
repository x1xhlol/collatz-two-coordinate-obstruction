import FirstHitPartialBounds
import ClockCutoffBounds

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic

/-- The odd part of the actual first-hit weight. -/
noncomputable def oddFirstHitWeight (N q : ℕ) : ℝ :=
  if q % 2 = 1 then firstHitWeight N q else 0

/-- Actual first-hit odd-source depth on the basin, extended by zero outside. -/
noncomputable def firstHitOddDepth (N q : ℕ) : ℕ := by
  classical
  exact if hh : ∃ A, iterate A q = N then oddCount (firstHitTime hh) q else 0

theorem oddFirstHitWeight_bounds (N q : ℕ) :
    0 ≤ oddFirstHitWeight N q ∧ oddFirstHitWeight N q ≤ 1 := by
  unfold oddFirstHitWeight
  split_ifs
  · exact firstHitWeight_bounds N q
  · norm_num

theorem firstHitOddDepth_of_first_hit {q N τ : ℕ} (hfirst : FirstHit q N τ) :
    firstHitOddDepth N q = oddCount τ q := by
  classical
  have hh : ∃ A, iterate A q = N := ⟨τ, hfirst.1⟩
  have ht := firstHit_time_unique (firstHitTime_spec hh) hfirst
  simp only [firstHitOddDepth, dif_pos hh, ht]

theorem actual_clock_term_eq {N : ℕ} (hN : 0 < N) (K n : ℕ) :
    CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n =
      firstHitPartialTerm K N (n + 1) / N := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hq : 0 < n + 1 := Nat.succ_pos n
  have hqr : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  by_cases hh : ∃ A, iterate A (n + 1) = N
  · have hf := firstHitTime_spec hh
    rw [firstHitPartialTerm_of_first_hit hf K]
    unfold CollatzCanonical.ClockSqueeze.clockTerm
    rw [firstHitOddDepth_of_first_hit hf]
    unfold oddFirstHitWeight
    by_cases ho : (n + 1) % 2 = 1
    · simp only [ho, if_true, true_and]
      split_ifs
      · rw [orbitRatio_first_hit hq hf]
        field_simp
      · simp
    · simp [ho]
  · simp [CollatzCanonical.ClockSqueeze.clockTerm, firstHitOddDepth, firstHitPartialTerm,
      oddFirstHitWeight, firstHitWeight, hh]

theorem actual_clock_summable {N : ℕ} (hN : 0 < N) (K : ℕ) :
    Summable (CollatzCanonical.ClockSqueeze.clockTerm
      (oddFirstHitWeight N) (firstHitOddDepth N) K) := by
  have hs := ((firstHitPartialTerm_summable hN K).div_const (N : ℝ)).comp_injective
    (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  have he : CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K =
      fun n : ℕ => firstHitPartialTerm K N (n + 1) / N := by
    funext n
    exact actual_clock_term_eq hN K n
  rw [he]
  exact hs

/-- The generic positive-index clock sum is exactly F_N(K)/N. -/
theorem actual_clock_tsum {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑' n, CollatzCanonical.ClockSqueeze.clockTerm
      (oddFirstHitWeight N) (firstHitOddDepth N) K n) = firstHitPartialSum K N / N := by
  simp only [actual_clock_term_eq hN]
  rw [tsum_div_const]
  have hs := (firstHitPartialTerm_summable hN K).tsum_eq_zero_add
  have hz : firstHitPartialTerm K N 0 = 0 := by simp [firstHitPartialTerm]
  rw [hz, zero_add] at hs
  exact congrArg (fun x : ℝ => x / N) hs.symm

noncomputable def firstHitLogCutoff (N K : ℕ) : ℝ :=
  Real.log N + 6 * (K : ℝ) * Real.log 2

theorem firstHitLogCutoff_eq_log {N : ℕ} (hN : 0 < N) (K : ℕ) :
    firstHitLogCutoff N K = Real.log ((N * 2 ^ (6 * K) : ℕ) : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, firstHitLogCutoff]
  rw [Real.log_mul hNr (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
  push_cast
  ring

theorem firstHitLogCutoff_nonneg {N : ℕ} (hN : 0 < N) (K : ℕ) :
    0 ≤ firstHitLogCutoff N K := by
  unfold firstHitLogCutoff
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn := Real.log_nonneg hN'
  have ht := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem firstHitLogCutoff_lt_log_iff {N q : ℕ} (hN : 0 < N) (hq : 0 < q) (K : ℕ) :
    firstHitLogCutoff N K < Real.log q ↔ N * 2 ^ (6 * K) < q := by
  rw [firstHitLogCutoff_eq_log hN K, Real.log_lt_log_iff (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

theorem actual_clock_tail_term_eq {N : ℕ} (hN : 0 < N) (K n : ℕ) :
    (if firstHitLogCutoff N K < Real.log (n + 1 : ℕ) then
      CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n else 0) =
        firstHitPartialTailTerm K N (n + 1) / N := by
  simp only [firstHitLogCutoff_lt_log_iff hN (Nat.succ_pos n), actual_clock_term_eq hN,
    firstHitPartialTailTerm]
  split_ifs <;> simp

theorem actual_clock_tail_summable {N : ℕ} (hN : 0 < N) (K : ℕ) :
    Summable (fun n : ℕ => if firstHitLogCutoff N K < Real.log (n + 1 : ℕ) then
      CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n else 0) := by
  have hs := ((firstHitPartialTailTerm_summable hN K).div_const (N : ℝ)).comp_injective
    (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  simpa only [Function.comp_def, actual_clock_tail_term_eq hN] using hs

/-- Exact identification of the generic logarithmic cutoff tail. -/
theorem actual_clock_tail_tsum {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑' n : ℕ, if firstHitLogCutoff N K < Real.log (n + 1 : ℕ) then
      CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n else 0) =
        (∑' q : ℕ, firstHitPartialTailTerm K N q) / N := by
  simp only [actual_clock_tail_term_eq hN]
  rw [tsum_div_const]
  have hs := (firstHitPartialTailTerm_summable hN K).tsum_eq_zero_add
  have hz : firstHitPartialTailTerm K N 0 = 0 := by simp [firstHitPartialTailTerm]
  rw [hz, zero_add] at hs
  exact congrArg (fun x : ℝ => x / N) hs.symm

theorem actual_clock_tail_bound {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑' n : ℕ, if firstHitLogCutoff N K < Real.log (n + 1 : ℕ) then
      CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n else 0) ≤
        ((9 / 8 : ℝ) / N) * (64 / 81 : ℝ) ^ K := by
  rw [actual_clock_tail_tsum hN K]
  calc
    _ ≤ ((9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K) / N :=
      div_le_div_of_nonneg_right (first_hit_partial_tail_bound hN K) (Nat.cast_nonneg N)
    _ = _ := by ring

theorem actual_clock_tail_tendsto_zero {N : ℕ} (hN : 0 < N) :
    Tendsto (fun K : ℕ => ∑' n : ℕ,
      if firstHitLogCutoff N K < Real.log (n + 1 : ℕ) then
        CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n else 0)
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro K
    rw [actual_clock_tail_tsum hN K]
    exact div_nonneg (tsum_nonneg (firstHitPartialTailTerm_nonneg K N)) (Nat.cast_nonneg N)
  · exact actual_clock_tail_bound hN
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 64 / 81) (by norm_num : (64 / 81 : ℝ) < 1)).const_mul
      ((9 / 8 : ℝ) / N)

/-- The normalized tail required by the generic weighted clock squeeze. -/
theorem actual_clock_normalized_tail_tendsto_zero {N : ℕ} (hN : 0 < N) :
    Tendsto (fun K : ℕ => (∑' n : ℕ,
      if (6 * Real.log 2) * (K : ℝ) + Real.log N < Real.log (n + 1 : ℕ) then
        CollatzCanonical.ClockSqueeze.clockTerm (oddFirstHitWeight N) (firstHitOddDepth N) K n else 0) /
          (K : ℝ)) atTop (𝓝 0) := by
  have h := (actual_clock_tail_tendsto_zero hN).mul
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [mul_zero] at h
  convert h using 1
  funext K
  have he : (6 * Real.log 2) * (K : ℝ) + Real.log N = firstHitLogCutoff N K := by
    unfold firstHitLogCutoff
    ring
  rw [he]
  ring

end CollatzCylinderPacking.Arithmetic
