import ArithmeticCylinderLaw

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- Parse the actual shortcut path, recording inverse blocks in reverse order.
An even final step extends the first inverse block; an odd final step starts one. -/
def pathTuple : ℕ → ℕ → List ℕ
  | 0, _ => []
  | A + 1, q => if iterate A q % 2 = 1 then 1 :: pathTuple A q else bumpHead (pathTuple A q)

theorem validBlock_of_odd_step {m : ℕ} (hm : m % 2 = 1) :
    ValidBlock 1 (step m) ∧ inverseValue 1 (step m) = m := by
  have hs := step_odd hm
  have he : 2 ^ 1 * step m - 1 = 3 * m := by norm_num; omega
  constructor
  · exact ⟨by decide, by rw [he]; exact dvd_mul_right 3 m⟩
  · simp only [inverseValue, he, Nat.mul_div_cancel_left _ (by decide : 0 < 3)]

theorem validBlock_extend_even {a m : ℕ} (hm : m % 2 = 0)
    (ha : ValidBlock a m) :
    ValidBlock (a + 1) (step m) ∧ inverseValue (a + 1) (step m) = inverseValue a m := by
  have hs := step_even hm
  have he : 2 ^ (a + 1) * step m = 2 ^ a * m := by rw [pow_succ, Nat.mul_assoc, hs]
  constructor
  · exact ⟨by omega, by simpa only [he] using ha.2⟩
  · simp only [inverseValue, he]

/-- Every actual path from a positive odd start has an admissible inverse
block tuple, with its exact elapsed time, odd-source count, and endpoint. -/
theorem pathTuple_spec (A : ℕ) {q : ℕ} (_hq : 0 < q) (hodd : q % 2 = 1) :
    ValidTuple (iterate A q) (pathTuple A q) ∧
      tupleEndpoint (iterate A q) (pathTuple A q) = q ∧
      (pathTuple A q).sum = A ∧ (pathTuple A q).length = oddCount A q := by
  induction A with
  | zero => simp [pathTuple, ValidTuple, tupleEndpoint, iterate, oddCount]
  | succ A ih =>
    by_cases ho : iterate A q % 2 = 1
    · have hb := validBlock_of_odd_step ho
      have hi : inverseValue 1 (step (iterate A q)) = iterate A q := hb.2
      simp only [pathTuple, ho, if_true, iterate, ValidTuple, tupleEndpoint,
        List.sum_cons, List.length_cons, oddCount]
      rw [hi]
      refine ⟨⟨hb.1, ih.1⟩, ih.2.1, ?_, ?_⟩
      · rw [ih.2.2.1]; omega
      · rw [ih.2.2.2]
    · have he : iterate A q % 2 = 0 := by omega
      cases ht : pathTuple A q with
      | nil =>
        have hA : A = 0 := by simpa only [ht, List.sum_nil] using ih.2.2.1.symm
        subst A
        simp only [iterate] at he
        omega
      | cons a as =>
        rw [ht] at ih
        have hb := validBlock_extend_even he ih.1.1
        simp only [pathTuple, he, Nat.zero_ne_one, if_false, ht, bumpHead, iterate, ValidTuple,
          tupleEndpoint, List.sum_cons, List.length_cons, oddCount, Nat.add_zero]
        rw [hb.2]
        refine ⟨⟨hb.1, ih.1.2⟩, ih.2.1, ?_, ih.2.2.2⟩
        have hs := ih.2.2.1
        simp only [List.sum_cons] at hs
        omega

/-- Finite hitting-path form, with an arbitrary positive final target. -/
theorem hitting_path_tuple {A q N : ℕ} (hq : 0 < q) (hodd : q % 2 = 1)
    (hhit : iterate A q = N) :
    ValidTuple N (pathTuple A q) ∧ tupleEndpoint N (pathTuple A q) = q ∧
      (pathTuple A q).sum = A ∧ (pathTuple A q).length = oddCount A q := by
  simpa only [hhit] using pathTuple_spec A hq hodd

/-- Every positive exponent list has the existing geometric-word encoding. -/
theorem exists_word_of_positive_list (as : List ℕ) (hpos : ∀ a ∈ as, 0 < a) :
    ∃ w : GeometricWord as.length, wordList as.length w = as := by
  induction as with
  | nil => exact ⟨(), rfl⟩
  | cons a as ih =>
    have ha := hpos a (by simp)
    have htail : ∀ b ∈ as, 0 < b := fun b hb => hpos b (by simp [hb])
    obtain ⟨w, hw⟩ := ih htail
    refine ⟨(a - 1, w), ?_⟩
    simp only [wordList, hw]
    congr 1
    omega

/-- The finite hitting path is represented by an actual ValidWord, including
paths ending at an even target before the last odd block is complete. -/
theorem hitting_path_word {A q N : ℕ} (hq : 0 < q) (hodd : q % 2 = 1)
    (hhit : iterate A q = N) :
    ∃ w : GeometricWord (oddCount A q), ValidWord (oddCount A q) N w ∧
      wordLength (oddCount A q) w = A ∧ tupleEndpoint N (wordList (oddCount A q) w) = q := by
  obtain ⟨hv, he, hs, hl⟩ := hitting_path_tuple hq hodd hhit
  obtain ⟨w, hw⟩ := exists_word_of_positive_list (pathTuple A q) (validTuple_positive hv)
  rw [← hl]
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [ValidWord, hw] using hv
  · rw [← wordList_sum, hw, hs]
  · simpa only [hw] using he

/-- First hitting time for the shortcut map. -/
def FirstHit (q N A : ℕ) : Prop := iterate A q = N ∧ ∀ i < A, iterate i q ≠ N

theorem first_hit_word {A q N : ℕ} (hq : 0 < q) (hodd : q % 2 = 1)
    (hfirst : FirstHit q N A) :
    ∃ w : GeometricWord (oddCount A q), ValidWord (oddCount A q) N w ∧
      wordLength (oddCount A q) w = A ∧ tupleEndpoint N (wordList (oddCount A q) w) = q :=
  hitting_path_word hq hodd hfirst.1

end CollatzCylinderPacking.Arithmetic
