import ActualWordDepth

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

open Classical in

/-- The odd-endpoint first-hit contribution with odd-source depth at most K. -/
noncomputable def firstHitPartialTerm (K N q : ℕ) : ℝ := by
  classical
  exact if q % 2 = 1 then
    if hh : ∃ A, iterate A q = N then
      if oddCount (firstHitTime hh) q ≤ K then orbitRatio (firstHitTime hh) q else 0
    else 0
  else 0

/-- The actual first-hit partial sum used by the cylinder reconstruction. -/
noncomputable def firstHitPartialSum (K N : ℕ) : ℝ :=
  ∑' q : ℕ, firstHitPartialTerm K N q

theorem firstHitPartialTerm_nonneg (K N q : ℕ) : 0 ≤ firstHitPartialTerm K N q := by
  unfold firstHitPartialTerm
  split_ifs
  · exact (orbitRatio_pos _ _).le
  all_goals exact le_rfl

theorem firstHitPartialTerm_of_first_hit {q N τ : ℕ} (hfirst : FirstHit q N τ) (K : ℕ) :
    firstHitPartialTerm K N q =
      if q % 2 = 1 ∧ oddCount τ q ≤ K then orbitRatio τ q else 0 := by
  classical
  have hh : ∃ A, iterate A q = N := ⟨τ, hfirst.1⟩
  have he : firstHitTime hh = τ := firstHit_time_unique (firstHitTime_spec hh) hfirst
  simp only [firstHitPartialTerm, dif_pos hh, he]
  split_ifs <;> simp_all

open Classical in
theorem firstHitPartialTerm_eq_weight (K N q : ℕ) :
    firstHitPartialTerm K N q =
      if q % 2 = 1 ∧ ∃ A, FirstHit q N A ∧ oddCount A q ≤ K
      then (N : ℝ) * firstHitWeight N q / q else 0 := by
  classical
  by_cases hh : ∃ A, iterate A q = N
  · have hf := firstHitTime_spec hh
    rw [firstHitPartialTerm_of_first_hit hf K]
    have he : (∃ A, FirstHit q N A ∧ oddCount A q ≤ K) ↔
        oddCount (firstHitTime hh) q ≤ K := by
      constructor
      · rintro ⟨A, hA, hc⟩
        rwa [← firstHit_time_unique hf hA] at hc
      · intro hc
        exact ⟨_, hf, hc⟩
    rw [he]
    split_ifs with ho
    · exact orbitRatio_first_hit (by omega) hf
    · rfl
  · have hn : ¬ ∃ A, FirstHit q N A ∧ oddCount A q ≤ K := by
      rintro ⟨A, hA, _⟩
      exact hh ⟨A, hA.1⟩
    simp [firstHitPartialTerm, hh, hn]

theorem firstHitPartialTerm_summable {N : ℕ} (hN : 0 < N) (K : ℕ) :
    Summable (firstHitPartialTerm K N) := by
  have hs := (odd_cumulative_hit_summable hN K).prod
  apply Summable.of_nonneg_of_le (firstHitPartialTerm_nonneg K N) _ hs
  intro q
  classical
  by_cases hh : ∃ A, iterate A q = N
  · have hf := firstHitTime_spec hh
    rw [firstHitPartialTerm_of_first_hit hf K]
    by_cases ho : q % 2 = 1 ∧ oddCount (firstHitTime hh) q ≤ K
    · rw [if_pos ho]
      have hrow := (odd_cumulative_hit_summable hN K).prod_factor q
      have he : oddCumulativeHitTerm K N (q, firstHitTime hh) =
          orbitRatio (firstHitTime hh) q := by
        simp [oddCumulativeHitTerm, ho.1, hf.1, ho.2]
      rw [← he]
      simpa using hrow.sum_le_tsum ({firstHitTime hh} : Finset ℕ)
        (fun A _ => oddCumulativeHitTerm_nonneg K N (q, A))
    · rw [if_neg ho]
      exact tsum_nonneg (fun A => oddCumulativeHitTerm_nonneg K N (q, A))
  · simp only [firstHitPartialTerm, dif_neg hh, ite_self]
    exact tsum_nonneg (fun A => oddCumulativeHitTerm_nonneg K N (q, A))

theorem odd_cumulative_no_return_hasSum {q N : ℕ}
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) (K : ℕ) :
    HasSum (fun A : ℕ => oddCumulativeHitTerm K N (q, A))
      (firstHitPartialTerm K N q) := by
  classical
  by_cases hh : ∃ A, iterate A q = N
  · have hf := firstHitTime_spec hh
    have he : oddCumulativeHitTerm K N (q, firstHitTime hh) = firstHitPartialTerm K N q := by
      rw [firstHitPartialTerm_of_first_hit hf K]
      simp only [oddCumulativeHitTerm, hf.1, true_and]
    rw [← he]
    apply hasSum_single (firstHitTime hh)
    intro A hA
    unfold oddCumulativeHitTerm
    apply if_neg
    rintro ⟨_, hhit, _⟩
    exact hA ((hitting_time_iff_eq_first_of_no_return hf hno).mp hhit)
  · have he : (fun A : ℕ => oddCumulativeHitTerm K N (q, A)) = fun _ => (0 : ℝ) := by
      funext A
      unfold oddCumulativeHitTerm
      exact if_neg (fun h => hh ⟨A, h.2.1⟩)
    rw [he]
    simp only [firstHitPartialTerm, dif_neg hh, ite_self]
    exact hasSum_zero

/-- Exact reconstruction for a target with no positive return. -/
theorem arithmetic_cumulative_no_return {N : ℕ} (hN : 0 < N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (3 : ℝ) ^ k * arithmeticMass k N) =
      (if N % 2 = 0 then (1 : ℝ) else 0) + firstHitPartialSum K N := by
  rw [arithmetic_cumulative_word_identity hN K]
  congr 1
  apply tsum_congr
  intro q
  exact (odd_cumulative_no_return_hasSum hno K).tsum_eq

theorem oddCount_mul_period {N r : ℕ} (hreturn : iterate r N = N) (j : ℕ) :
    oddCount (j * r) N = j * oddCount r N := by
  induction j with
  | zero => simp [oddCount]
  | succ j ih =>
    rw [Nat.succ_mul, oddCount_add, iterate_mul_period hreturn, ih, Nat.succ_mul]

theorem oddCount_hit_plus_periods {q N τ r : ℕ} (hhit : iterate τ q = N)
    (hreturn : iterate r N = N) (j : ℕ) :
    oddCount (τ + j * r) q = oddCount τ q + j * oddCount r N := by
  rw [oddCount_add, hhit, oddCount_mul_period hreturn]

/-- Per-endpoint reconstruction of the depth-truncated all-hit sum as the
finite sum of its first-hit contribution followed by complete cycle loops. -/
theorem odd_cumulative_periodic_hasSum {q N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) (K : ℕ) :
    HasSum (fun A : ℕ => oddCumulativeHitTerm K N (q, A))
      (∑ j ∈ Finset.range (K / oddCount r N + 1),
        (orbitRatio r N) ^ j * firstHitPartialTerm (K - j * oddCount r N) N q) := by
  classical
  have hk : 0 < oddCount r N := positive_cycle_oddCount_pos hN hperiod.positive hperiod.returns
  by_cases hh : ∃ A, iterate A q = N
  · have hf := firstHitTime_spec hh
    let τ := firstHitTime hh
    let g : ℕ → ℕ := fun j => τ + j * r
    have hg : Function.Injective g := by
      intro i j he
      dsimp only [g] at he
      exact Nat.eq_of_mul_eq_mul_right hperiod.positive (Nat.add_left_cancel he)
    have hz (A : ℕ) (hA : A ∉ Set.range g) : oddCumulativeHitTerm K N (q, A) = 0 := by
      unfold oddCumulativeHitTerm
      apply if_neg
      rintro ⟨_, hhit, _⟩
      obtain ⟨j, hj⟩ := (hitting_time_iff_first_plus_periods hf hperiod).mp hhit
      exact hA ⟨j, hj.symm⟩
    apply (hg.hasSum_iff hz).mp
    have hzero (j : ℕ) (hj : j ∉ Finset.range (K / oddCount r N + 1)) :
        oddCumulativeHitTerm K N (q, g j) = 0 := by
      have hj' : K / oddCount r N < j := by simpa using hj
      have hprod : K < j * oddCount r N := (Nat.div_lt_iff_lt_mul hk).mp hj'
      unfold oddCumulativeHitTerm
      apply if_neg
      rintro ⟨_, _, hc⟩
      change oddCount (g j) q ≤ K at hc
      have he := oddCount_hit_plus_periods hf.1 hperiod.returns j
      change oddCount (g j) q = oddCount τ q + j * oddCount r N at he
      omega
    have hsum : HasSum (fun j : ℕ => oddCumulativeHitTerm K N (q, g j))
        (∑ j ∈ Finset.range (K / oddCount r N + 1), oddCumulativeHitTerm K N (q, g j)) :=
      hasSum_sum_of_ne_finset_zero hzero
    have heq : (∑ j ∈ Finset.range (K / oddCount r N + 1),
        oddCumulativeHitTerm K N (q, g j)) =
        ∑ j ∈ Finset.range (K / oddCount r N + 1),
          (orbitRatio r N) ^ j * firstHitPartialTerm (K - j * oddCount r N) N q := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ K / oddCount r N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hprod : j * oddCount r N ≤ K := (Nat.le_div_iff_mul_le hk).mp hj'
      have hhit : iterate (g j) q = N :=
        (hitting_time_iff_first_plus_periods hf hperiod).mpr ⟨j, rfl⟩
      have hc := oddCount_hit_plus_periods hf.1 hperiod.returns j
      have hw := orbitRatio_hit_plus_periods hf.1 hperiod.returns j
      change oddCount (g j) q = oddCount τ q + j * oddCount r N at hc
      change orbitRatio (g j) q = orbitRatio τ q * orbitRatio r N ^ j at hw
      rw [firstHitPartialTerm_of_first_hit hf]
      simp only [oddCumulativeHitTerm, hhit, true_and, hc]
      have hle : oddCount τ q + j * oddCount r N ≤ K ↔
          oddCount τ q ≤ K - j * oddCount r N := by omega
      simp only [hle]
      split_ifs
      · exact hw.trans (mul_comm _ _)
      · simp
    simpa only [Function.comp_def, heq] using hsum
  · have he : (fun A : ℕ => oddCumulativeHitTerm K N (q, A)) = fun _ => (0 : ℝ) := by
      funext A
      unfold oddCumulativeHitTerm
      exact if_neg (fun h => hh ⟨A, h.2.1⟩)
    rw [he]
    simp only [firstHitPartialTerm, dif_neg hh, ite_self, mul_zero, Finset.sum_const_zero]
    exact hasSum_zero

/-- Exact arithmetic-cylinder reconstruction for an actual periodic target.
The only separate singleton is the empty inverse word when N is even. -/
theorem arithmetic_cumulative_periodic {N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (3 : ℝ) ^ k * arithmeticMass k N) =
      (if N % 2 = 0 then (1 : ℝ) else 0) +
        ∑ j ∈ Finset.range (K / oddCount r N + 1),
          (orbitRatio r N) ^ j * firstHitPartialSum (K - j * oddCount r N) N := by
  rw [arithmetic_cumulative_word_identity hN K]
  congr 1
  have he : (∑' q : ℕ, ∑' A : ℕ, oddCumulativeHitTerm K N (q, A)) =
      ∑' q : ℕ, ∑ j ∈ Finset.range (K / oddCount r N + 1),
        (orbitRatio r N) ^ j * firstHitPartialTerm (K - j * oddCount r N) N q := by
    apply tsum_congr
    intro q
    exact (odd_cumulative_periodic_hasSum hN hperiod K).tsum_eq
  rw [he, Summable.tsum_finsetSum
    (fun j _ => (firstHitPartialTerm_summable hN _).mul_left ((orbitRatio r N) ^ j))]
  apply Finset.sum_congr rfl
  intro j _
  exact tsum_mul_left

end CollatzCylinderPacking.Arithmetic
