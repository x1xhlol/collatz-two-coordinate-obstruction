import ActualCycleWeights
import ArithmeticCylinderGrowth
import FirstHitEndpointTail

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The actual odd-source count of an arithmetic inverse word. -/
theorem valid_word_oddCount {k N : ℕ} (hN : 0 < N)
    {w : GeometricWord k} (hv : ValidWord k N w) :
    oddCount (wordLength k w) (tupleEndpoint N (wordList k w)) = k := by
  have hp := valid_tuple_path hN hv
  have hc := congrArg List.sum hp.2.2.1
  simpa only [reverseItinerary_sum, encode_sum, wordList_length, wordList_sum] using hc

/-- A valid positive-depth word is determined by its endpoint and elapsed time. -/
theorem valid_word_endpoint_time_injective {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    Function.Injective (fun w : {w : GeometricWord k // ValidWord k N w} =>
      (tupleEndpoint N (wordList k w.val), wordLength k w.val)) := by
  intro w v he
  apply Subtype.ext
  apply wordList_injective k
  apply admissible_endpoint_injective (valid_word_admissible hk hN w.property)
    (valid_word_admissible hk hN v.property)
  · simpa only [wordList_sum] using congrArg Prod.snd he
  · exact congrArg Prod.fst he

/-- A hit of the target at a specified time, restricted to odd starts and
the exact odd-source depth. -/
noncomputable def oddDepthHitTerm (k N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 % 2 = 1 ∧ iterate p.2 p.1 = N ∧ oddCount p.2 p.1 = k
    then orbitRatio p.2 p.1 else 0

theorem oddDepthHitTerm_nonneg (k N : ℕ) (p : ℕ × ℕ) :
    0 ≤ oddDepthHitTerm k N p := by
  unfold oddDepthHitTerm
  split_ifs
  · exact (orbitRatio_pos _ _).le
  · exact le_rfl

/-- The countable arithmetic word sum is exactly the sum over all odd
starting endpoints and actual hitting times at this depth. -/
theorem odd_depth_hit_hasSum {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    HasSum (oddDepthHitTerm k N) ((3 : ℝ) ^ k * arithmeticMass k N) := by
  classical
  let g : {w : GeometricWord k // ValidWord k N w} → ℕ × ℕ :=
    fun w => (tupleEndpoint N (wordList k w.val), wordLength k w.val)
  have hg : Function.Injective g := valid_word_endpoint_time_injective hk hN
  have hz (p : ℕ × ℕ) (hp : p ∉ Set.range g) : oddDepthHitTerm k N p = 0 := by
    unfold oddDepthHitTerm
    apply if_neg
    rintro ⟨ho, hh, hc⟩
    have hq : 0 < p.1 := by omega
    have hex := hitting_path_word hq ho hh
    rw [hc] at hex
    obtain ⟨w, hv, hl, he⟩ := hex
    exact hp ⟨⟨w, hv⟩, Prod.ext he hl⟩
  apply (hg.hasSum_iff hz).mp
  have hsub : HasSum (fun w : {w : GeometricWord k // ValidWord k N w} =>
      (3 : ℝ) ^ k * arithmeticTerm k N w.val)
      ((3 : ℝ) ^ k * arithmeticMass k N) := by
    apply (hasSum_subtype_iff_of_support_subset (s := {w | ValidWord k N w}) ?_).mpr
      ((arithmeticTerm_summable k N).hasSum.mul_left ((3 : ℝ) ^ k))
    intro w hw
    by_contra hv
    change ¬ ValidWord k N w at hv
    exact hw (by simp [arithmeticTerm, hv])
  convert hsub using 1
  funext w
  have hp := valid_tuple_path hN w.property
  have ho := hp.2.2.2 (wordList_ne_nil hk w.val)
  have hh := hp.2.1
  rw [wordList_sum] at hh
  have hc := valid_word_oddCount hN w.property
  simp only [Function.comp_def, g, oddDepthHitTerm, ho, hh, hc, and_self, if_true,
    arithmeticTerm, w.property, orbitRatio, one_div_pow, mul_one_div]

theorem odd_depth_hit_tsum {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    (∑' q : ℕ, ∑' A : ℕ, oddDepthHitTerm k N (q, A)) =
      (3 : ℝ) ^ k * arithmeticMass k N := by
  rw [← (odd_depth_hit_hasSum hk hN).summable.tsum_prod]
  exact (odd_depth_hit_hasSum hk hN).tsum_eq

theorem odd_depth_zero_hasSum (N : ℕ) :
    HasSum (oddDepthHitTerm 0 N) (if N % 2 = 1 then (1 : ℝ) else 0) := by
  have hv : oddDepthHitTerm 0 N (N, 0) = if N % 2 = 1 then (1 : ℝ) else 0 := by
    simp [oddDepthHitTerm, iterate, oddCount, orbitRatio]
  rw [← hv]
  apply hasSum_single (N, 0)
  intro p hp
  unfold oddDepthHitTerm
  apply if_neg
  rintro ⟨ho, hh, hc⟩
  have hA : p.2 = 0 := by
    by_contra hn
    have hpos := oddCount_pos_of_odd_start (Nat.pos_of_ne_zero hn) ho
    omega
  have hq : p.1 = N := by simpa only [hA, iterate] using hh
  exact hp (Prod.ext hq hA)

theorem odd_depth_hit_summable {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Summable (oddDepthHitTerm k N) := by
  cases k with
  | zero => exact (odd_depth_zero_hasSum N).summable
  | succ k => exact (odd_depth_hit_hasSum (Nat.succ_pos k) hN).summable

/-- All odd-start hitting contributions with at most K odd sources. -/
noncomputable def oddCumulativeHitTerm (K N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 % 2 = 1 ∧ iterate p.2 p.1 = N ∧ oddCount p.2 p.1 ≤ K
    then orbitRatio p.2 p.1 else 0

theorem oddCumulativeHitTerm_eq_sum (K N : ℕ) (p : ℕ × ℕ) :
    oddCumulativeHitTerm K N p =
      ∑ k ∈ Finset.range (K + 1), oddDepthHitTerm k N p := by
  classical
  by_cases ho : p.1 % 2 = 1
  · by_cases hh : iterate p.2 p.1 = N
    · simp only [oddCumulativeHitTerm, oddDepthHitTerm, ho, hh, true_and]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range, Nat.lt_succ_iff]
    · simp [oddCumulativeHitTerm, oddDepthHitTerm, hh]
  · simp [oddCumulativeHitTerm, oddDepthHitTerm, ho]

theorem odd_cumulative_hit_summable {N : ℕ} (hN : 0 < N) (K : ℕ) :
    Summable (oddCumulativeHitTerm K N) := by
  have he : oddCumulativeHitTerm K N =
      fun p => ∑ k ∈ Finset.range (K + 1), oddDepthHitTerm k N p := by
    funext p
    exact oddCumulativeHitTerm_eq_sum K N p
  rw [he]
  exact summable_sum (fun k _ => odd_depth_hit_summable hN k)

theorem oddCumulativeHitTerm_nonneg (K N : ℕ) (p : ℕ × ℕ) :
    0 ≤ oddCumulativeHitTerm K N p := by
  unfold oddCumulativeHitTerm
  split_ifs
  · exact (orbitRatio_pos _ _).le
  · exact le_rfl

/-- The empty word at an even target is the sole contribution excluded by
the restriction to odd starting endpoints. -/
theorem arithmetic_cumulative_word_identity {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (3 : ℝ) ^ k * arithmeticMass k N) =
      (if N % 2 = 0 then (1 : ℝ) else 0) +
        ∑' q : ℕ, ∑' A : ℕ, oddCumulativeHitTerm K N (q, A) := by
  classical
  rw [← (odd_cumulative_hit_summable hN K).tsum_prod]
  have he : (∑' p : ℕ × ℕ, oddCumulativeHitTerm K N p) =
      ∑ k ∈ Finset.range (K + 1), ∑' p : ℕ × ℕ, oddDepthHitTerm k N p := by
    simp only [oddCumulativeHitTerm_eq_sum]
    exact Summable.tsum_finsetSum (fun k _ => odd_depth_hit_summable hN k)
  rw [he, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : arithmeticMass 0 N = 1 := by
    simp [arithmeticMass, arithmeticTerm, GeometricWord, wordList, ValidWord,
      ValidTuple, wordLength]
  rw [(odd_depth_zero_hasSum N).tsum_eq, hz]
  have hs : (∑ k ∈ Finset.range K, (3 : ℝ) ^ (k + 1) * arithmeticMass (k + 1) N) =
      ∑ k ∈ Finset.range K, ∑' p : ℕ × ℕ, oddDepthHitTerm (k + 1) N p := by
    apply Finset.sum_congr rfl
    intro k _
    exact (odd_depth_hit_hasSum (Nat.succ_pos k) hN).tsum_eq.symm
  rw [hs]
  have hn : N % 2 = 0 ∨ N % 2 = 1 := by omega
  rcases hn with hn | hn <;> simp [hn, add_comm]

end CollatzCylinderPacking.Arithmetic
