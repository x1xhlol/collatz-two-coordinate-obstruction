import ActualFirstHitReconstruction

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The part of the actual first-hit sum above the uniform height cutoff. -/
noncomputable def firstHitPartialTailTerm (K N q : ℕ) : ℝ :=
  if N * 2 ^ (6 * K) < q then firstHitPartialTerm K N q else 0

theorem firstHitPartialTailTerm_nonneg (K N q : ℕ) :
    0 ≤ firstHitPartialTailTerm K N q := by
  unfold firstHitPartialTailTerm
  split_ifs
  · exact firstHitPartialTerm_nonneg K N q
  · exact le_rfl

theorem firstHitPartialTailTerm_summable {N : ℕ} (hN : 0 < N) (K : ℕ) :
    Summable (firstHitPartialTailTerm K N) := by
  apply Summable.of_nonneg_of_le (firstHitPartialTailTerm_nonneg K N) _
    (firstHitPartialTerm_summable hN K)
  intro q
  unfold firstHitPartialTailTerm
  split_ifs
  · exact le_rfl
  · exact firstHitPartialTerm_nonneg K N q

/-- Countable endpoint tail for the actual first-hit partial sum. -/
theorem first_hit_partial_tail_bound {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑' q : ℕ, firstHitPartialTailTerm K N q) ≤
      (9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K := by
  classical
  apply (firstHitPartialTailTerm_summable hN K).tsum_le_of_sum_le
  intro S
  let Q := S.filter (fun q => N * 2 ^ (6 * K) < q ∧
    q % 2 = 1 ∧ ∃ A, FirstHit q N A ∧ oddCount A q ≤ K)
  have hs (q : ℕ) (hq : q ∈ Q) :
      N * 2 ^ (6 * K) < q ∧ q % 2 = 1 ∧ ∃ A, FirstHit q N A ∧ oddCount A q ≤ K :=
    (Finset.mem_filter.mp hq).2
  let time : ℕ → ℕ := fun q => if hq : q ∈ Q then Classical.choose (hs q hq).2.2 else 0
  have ht (q : ℕ) (hq : q ∈ Q) : FirstHit q N (time q) ∧ oddCount (time q) q ≤ K := by
    simp only [time, dif_pos hq]
    exact Classical.choose_spec (hs q hq).2.2
  have hb := first_hit_finite_family_tail hN K Q time
    (fun q hq => by have ho := (hs q hq).2.1; omega)
    (fun q hq => (hs q hq).2.1)
    (fun q hq => (ht q hq).1)
    (fun q hq => (ht q hq).2)
    (fun q hq => (hs q hq).1)
  have he : (∑ q ∈ S, firstHitPartialTailTerm K N q) =
      ∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q := by
    dsimp only [Q]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    rw [firstHitPartialTailTerm, firstHitPartialTerm_eq_weight]
    split_ifs <;> simp_all
  exact he.trans_le hb

theorem first_hit_partial_endpoint_tail {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑' q : ℕ, if N * 2 ^ (6 * K) < q then firstHitPartialTerm K N q else 0) ≤
      (9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K :=
  first_hit_partial_tail_bound hN K

theorem firstHitPartialTerm_le_reciprocal (K N q : ℕ) :
    firstHitPartialTerm K N q ≤ (N : ℝ) / q := by
  classical
  rw [firstHitPartialTerm_eq_weight]
  split_ifs
  · have hb := (firstHitWeight_bounds N q).2
    calc
      (N : ℝ) * firstHitWeight N q / q ≤ (N : ℝ) * 1 / q := by gcongr
      _ = (N : ℝ) / q := by ring
  · positivity

/-- A finite reciprocal sum, with its zero denominator excluded. -/
noncomputable def positiveReciprocalSum (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, (1 : ℝ) / (i + 1 : ℕ)

theorem positiveReciprocalSum_le_nat (M : ℕ) : positiveReciprocalSum M ≤ M := by
  unfold positiveReciprocalSum
  calc
    (∑ i ∈ Finset.range M, (1 : ℝ) / (i + 1 : ℕ)) ≤ ∑ _i ∈ Finset.range M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast Nat.succ_pos i
    _ = M := by simp

/-- Each doubling of the endpoint cutoff adds at most one harmonic unit. -/
theorem positiveReciprocalSum_double {M : ℕ} (hM : 0 < M) :
    positiveReciprocalSum (2 * M) ≤ positiveReciprocalSum M + 1 := by
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  unfold positiveReciprocalSum
  rw [two_mul, Finset.sum_range_add]
  apply add_le_add le_rfl
  calc
    (∑ i ∈ Finset.range M, (1 : ℝ) / ((M + i) + 1 : ℕ)) ≤
        ∑ _i ∈ Finset.range M, (1 : ℝ) / M := by
      apply Finset.sum_le_sum
      intro i _
      apply one_div_le_one_div_of_le hM'
      exact_mod_cast (by omega : M ≤ M + i + 1)
    _ = 1 := by simp [ne_of_gt hM']

theorem positiveReciprocalSum_dyadic {N : ℕ} (hN : 0 < N) (L : ℕ) :
    positiveReciprocalSum (N * 2 ^ L) ≤ (N : ℝ) + L := by
  induction L with
  | zero => simpa using positiveReciprocalSum_le_nat N
  | succ L ih =>
    have hM : 0 < N * 2 ^ L := by positivity
    have hb := positiveReciprocalSum_double hM
    have he : N * 2 ^ (L + 1) = 2 * (N * 2 ^ L) := by rw [pow_succ]; ring
    rw [he]
    exact hb.trans (by push_cast; linarith)

theorem firstHitPartialSum_split {N : ℕ} (hN : 0 < N) (K : ℕ) :
    firstHitPartialSum K N =
      (∑ q ∈ Finset.range (N * 2 ^ (6 * K) + 1), firstHitPartialTerm K N q) +
        ∑' q : ℕ, firstHitPartialTailTerm K N q := by
  classical
  have he := (firstHitPartialTerm_summable hN K).sum_add_tsum_subtype_compl
    (Finset.range (N * 2 ^ (6 * K) + 1))
  have hf : (∑' q : {q : ℕ // q ∉ Finset.range (N * 2 ^ (6 * K) + 1)},
      firstHitPartialTerm K N q.val) = ∑' q : ℕ, firstHitPartialTailTerm K N q := by
    calc
      _ = ∑' q : ℕ, ({q : ℕ | q ∉ Finset.range (N * 2 ^ (6 * K) + 1)} : Set ℕ).indicator
          (firstHitPartialTerm K N) q :=
        tsum_subtype {q : ℕ | q ∉ Finset.range (N * 2 ^ (6 * K) + 1)} (firstHitPartialTerm K N)
      _ = _ := by
        apply tsum_congr
        intro q
        simp only [Set.indicator, Set.mem_setOf_eq, Finset.mem_range,
          Nat.not_lt, firstHitPartialTailTerm]
        congr 1
  rw [hf] at he
  exact he.symm

/-- A linear bound for the actual first-hit partial sum, derived without
the clock law or a density hypothesis. -/
theorem first_hit_partial_sum_linear_bound {N : ℕ} (hN : 0 < N) (K : ℕ) :
    firstHitPartialSum K N ≤ ((N : ℝ) * (N + 6) + 9 / 8) * (K + 1) := by
  have hhead : (∑ q ∈ Finset.range (N * 2 ^ (6 * K) + 1), firstHitPartialTerm K N q) ≤
      (N : ℝ) * ((N : ℝ) + 6 * K) := by
    calc
      (∑ q ∈ Finset.range (N * 2 ^ (6 * K) + 1), firstHitPartialTerm K N q) ≤
          ∑ q ∈ Finset.range (N * 2 ^ (6 * K) + 1), (N : ℝ) / q :=
        Finset.sum_le_sum (fun q _ => firstHitPartialTerm_le_reciprocal K N q)
      _ = (N : ℝ) * positiveReciprocalSum (N * 2 ^ (6 * K)) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, div_zero, add_zero, positiveReciprocalSum,
          Finset.mul_sum, mul_one_div]
      _ ≤ (N : ℝ) * ((N : ℝ) + 6 * K) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using positiveReciprocalSum_dyadic hN (6 * K)
  have htail := first_hit_partial_tail_bound hN K
  have hpow : (64 / 81 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [firstHitPartialSum_split hN K]
  have hK : (0 : ℝ) ≤ K := by positivity
  have hNr : (0 : ℝ) ≤ N := by positivity
  nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hK]

theorem first_hit_partial_sum_linear {N : ℕ} (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      0 ≤ firstHitPartialSum K N ∧ firstHitPartialSum K N ≤ C * (K + 1) := by
  refine ⟨(N : ℝ) * (N + 6) + 9 / 8, by positivity, ?_⟩
  intro K
  exact ⟨tsum_nonneg (firstHitPartialTerm_nonneg K N), first_hit_partial_sum_linear_bound hN K⟩

end CollatzCylinderPacking.Arithmetic
