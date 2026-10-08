import ArithmeticCylinderLaw

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The actual arithmetic endpoint satisfies the homogeneous inverse bound. -/
theorem valid_word_endpoint_bound {k N : ℕ} (hN : 0 < N)
    {w : GeometricWord k} (hv : ValidWord k N w) :
    3 ^ k * tupleEndpoint N (wordList k w) ≤ 2 ^ wordLength k w * N := by
  have hp := valid_tuple_path hN hv
  have hc := congrArg List.sum hp.2.2.1
  simp only [reverseItinerary_sum, encode_sum, wordList_length, wordList_sum] at hc
  have hb := (scaled_bounds (wordLength k w) (tupleEndpoint N (wordList k w))).1
  have he := hp.2.1
  rw [wordList_sum] at he
  rwa [hc, he] at hb

/-- A height cutoff forces a total shortcut length cutoff for valid words. -/
theorem endpoint_cutoff_forces_length {k N H : ℕ} (hN : 0 < N)
    {w : GeometricWord k} (hv : ValidWord k N w)
    (hm : N * 2 ^ H < tupleEndpoint N (wordList k w)) :
    H < wordLength k w := by
  have hb := valid_word_endpoint_bound hN hv
  have hthree : 1 ≤ (3 : ℕ) ^ k := Nat.one_le_pow _ _ (by decide)
  have hm' : tupleEndpoint N (wordList k w) ≤ 2 ^ wordLength k w * N := by
    have hh := Nat.mul_le_mul_right (tupleEndpoint N (wordList k w)) hthree
    omega
  by_contra h
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt h)
  have hprod := Nat.mul_le_mul_right N hpow
  nlinarith

/-- Arithmetic inverse-word weight restricted to a lower length threshold. -/
noncomputable def arithmeticLengthTailTerm (k N H : ℕ) (w : GeometricWord k) : ℝ := by
  classical
  exact if H ≤ wordLength k w then arithmeticTerm k N w else 0

theorem arithmeticLengthTailTerm_nonneg (k N H : ℕ) (w : GeometricWord k) :
    0 ≤ arithmeticLengthTailTerm k N H w := by
  classical
  unfold arithmeticLengthTailTerm
  split_ifs
  · exact arithmeticTerm_nonneg k N w
  · exact le_rfl

theorem arithmetic_length_tail_summable (k N H : ℕ) :
    Summable (arithmeticLengthTailTerm k N H) := by
  apply Summable.of_nonneg_of_le (arithmeticLengthTailTerm_nonneg k N H) _
    (arithmeticTerm_summable k N)
  intro w
  unfold arithmeticLengthTailTerm
  split_ifs
  · exact le_rfl
  · exact arithmeticTerm_nonneg k N w

/-- Exponential Markov estimate before the inverse-branch factor 3^k. -/
theorem arithmetic_length_tail_bound (k N H : ℕ) :
    (∑' w : GeometricWord k, arithmeticLengthTailTerm k N H w) ≤
      (2 / 3 : ℝ) ^ H * (3 : ℝ) ^ k := by
  have ht := (geometric_word_tilted_mass k).mul_left ((2 / 3 : ℝ) ^ H)
  apply le_trans (Summable.tsum_le_tsum (g := fun w : GeometricWord k =>
    (2 / 3 : ℝ) ^ H * (3 / 4 : ℝ) ^ wordLength k w) _
      (arithmetic_length_tail_summable k N H) ht.summable) ht.tsum_eq.le
  intro w
  unfold arithmeticLengthTailTerm
  split_ifs with h
  · calc
      arithmeticTerm k N w ≤ (1 / 2 : ℝ) ^ wordLength k w :=
        arithmeticTerm_le_probability k N w
      _ = (2 / 3 : ℝ) ^ wordLength k w * (3 / 4 : ℝ) ^ wordLength k w := by
        rw [← mul_pow]
        norm_num
      _ ≤ (2 / 3 : ℝ) ^ H * (3 / 4 : ℝ) ^ wordLength k w :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) (by positivity)
  · positivity

/-- The weighted length tail used at depth k in the height growth estimate. -/
theorem arithmetic_six_depth_tail (k N : ℕ) :
    (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticLengthTailTerm k N (6 * k) w) ≤
      (64 / 81 : ℝ) ^ k := by
  calc
    (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticLengthTailTerm k N (6 * k) w) ≤
        (3 : ℝ) ^ k * ((2 / 3 : ℝ) ^ (6 * k) * (3 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (arithmetic_length_tail_bound k N (6 * k)) (by positivity)
    _ = (64 / 81 : ℝ) ^ k := by
      rw [pow_mul, ← mul_pow, ← mul_pow]
      norm_num

/-- Arithmetic inverse-word probability restricted by actual endpoint height. -/
noncomputable def arithmeticEndpointTailTerm (k N H : ℕ) (w : GeometricWord k) : ℝ := by
  classical
  exact if N * 2 ^ H < tupleEndpoint N (wordList k w) then arithmeticTerm k N w else 0

theorem arithmeticEndpointTailTerm_nonneg (k N H : ℕ) (w : GeometricWord k) :
    0 ≤ arithmeticEndpointTailTerm k N H w := by
  classical
  unfold arithmeticEndpointTailTerm
  split_ifs
  · exact arithmeticTerm_nonneg k N w
  · exact le_rfl

theorem arithmetic_endpoint_tail_summable (k N H : ℕ) :
    Summable (arithmeticEndpointTailTerm k N H) := by
  apply Summable.of_nonneg_of_le (arithmeticEndpointTailTerm_nonneg k N H) _
    (arithmeticTerm_summable k N)
  intro w
  unfold arithmeticEndpointTailTerm
  split_ifs
  · exact le_rfl
  · exact arithmeticTerm_nonneg k N w

theorem arithmetic_endpoint_tail_le_length_tail {k N H : ℕ} (hN : 0 < N) :
    (∑' w : GeometricWord k, arithmeticEndpointTailTerm k N H w) ≤
      ∑' w : GeometricWord k, arithmeticLengthTailTerm k N H w := by
  apply Summable.tsum_le_tsum _ (arithmetic_endpoint_tail_summable k N H)
    (arithmetic_length_tail_summable k N H)
  intro w
  classical
  by_cases hv : ValidWord k N w
  · unfold arithmeticEndpointTailTerm
    split_ifs with hm
    · have hl := (endpoint_cutoff_forces_length hN hv hm).le
      simp [arithmeticLengthTailTerm, hl]
    · exact arithmeticLengthTailTerm_nonneg k N H w
  · simp [arithmeticEndpointTailTerm, arithmeticLengthTailTerm, arithmeticTerm, hv]

/-- Endpoint-height tail at a fixed depth, including the inverse-branch factor. -/
theorem arithmetic_endpoint_tail_bound {k N H : ℕ} (hN : 0 < N) :
    (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticEndpointTailTerm k N H w) ≤
      (2 / 3 : ℝ) ^ H * (9 : ℝ) ^ k := by
  calc
    (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticEndpointTailTerm k N H w) ≤
        (3 : ℝ) ^ k * ((2 / 3 : ℝ) ^ H * (3 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left
        ((arithmetic_endpoint_tail_le_length_tail hN).trans
          (arithmetic_length_tail_bound k N H)) (by positivity)
    _ = (2 / 3 : ℝ) ^ H * (9 : ℝ) ^ k := by
      rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]
      ring

/-- Sum of inverse odd-block weights over depths 1 through K above N 2^(6K). -/
theorem arithmetic_endpoint_cutoff {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑ j ∈ Finset.range K, (3 : ℝ) ^ (j + 1) *
      (∑' w : GeometricWord (j + 1), arithmeticEndpointTailTerm (j + 1) N (6 * K) w)) ≤
      (9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K := by
  have hsum (K : ℕ) : (∑ j ∈ Finset.range K, (9 : ℝ) ^ (j + 1)) =
      (9 / 8 : ℝ) * ((9 : ℝ) ^ K - 1) := by
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  calc
    (∑ j ∈ Finset.range K, (3 : ℝ) ^ (j + 1) *
      (∑' w : GeometricWord (j + 1), arithmeticEndpointTailTerm (j + 1) N (6 * K) w)) ≤
        ∑ j ∈ Finset.range K, (2 / 3 : ℝ) ^ (6 * K) * (9 : ℝ) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact arithmetic_endpoint_tail_bound hN
    _ = (2 / 3 : ℝ) ^ (6 * K) * ((9 / 8 : ℝ) * ((9 : ℝ) ^ K - 1)) := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ (2 / 3 : ℝ) ^ (6 * K) * ((9 / 8 : ℝ) * (9 : ℝ) ^ K) := by
      gcongr
      linarith
    _ = (9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K := by
      rw [pow_mul]
      have he : (2 / 3 : ℝ) ^ 6 * 9 = 64 / 81 := by norm_num
      rw [← mul_assoc, mul_comm (((2 / 3 : ℝ) ^ 6) ^ K), mul_assoc, ← mul_pow, he]

end CollatzCylinderPacking.Arithmetic
