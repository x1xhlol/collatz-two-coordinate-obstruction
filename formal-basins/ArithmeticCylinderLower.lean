import ArithmeticCylinderLaw

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem validBlock_of_identity {a N m : ℕ} (ha : 0 < a)
    (h : 3 * m + 1 = 2 ^ a * N) : ValidBlock a N := by
  refine ⟨ha, ?_⟩
  have he : 2 ^ a * N - 1 = 3 * m := by omega
  rw [he]
  exact dvd_mul_right 3 m

theorem inverseValue_of_identity {a N m : ℕ}
    (h : 3 * m + 1 = 2 ^ a * N) : inverseValue a N = m := by
  have he : 2 ^ a * N - 1 = 3 * m := by omega
  simp [inverseValue, he]

theorem validTuple_ones (k b : ℕ) (hb : 0 < b) :
    ValidTuple (3 ^ k * b - 1) (List.replicate k 1) := by
  induction k generalizing b with
  | zero => simp [ValidTuple]
  | succ k ih =>
    have hp : 0 < 3 ^ k * b := by positivity
    have he : 3 ^ (k + 1) * b = 3 * (3 ^ k * b) := by rw [pow_succ]; ring
    have hid : 3 * (3 ^ k * (2 * b) - 1) + 1 =
        2 ^ 1 * (3 ^ (k + 1) * b - 1) := by
      have hm : 3 ^ k * (2 * b) = 2 * (3 ^ k * b) := by ring
      rw [he, hm]
      norm_num only [pow_one]
      omega
    rw [List.replicate_succ]
    change ValidBlock 1 (3 ^ (k + 1) * b - 1) ∧
      ValidTuple (inverseValue 1 (3 ^ (k + 1) * b - 1)) (List.replicate k 1)
    refine ⟨validBlock_of_identity (by decide) hid, ?_⟩
    rw [inverseValue_of_identity hid]
    exact ih (2 * b) (by omega)

def allOneWord : (k : ℕ) → GeometricWord k
  | 0 => ()
  | k + 1 => (0, allOneWord k)

theorem allOneWord_list (k : ℕ) : wordList k (allOneWord k) = List.replicate k 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [allOneWord, wordList, List.replicate_succ, ih]

theorem allOneWord_length (k : ℕ) : wordLength k (allOneWord k) = k := by
  rw [← wordList_sum, allOneWord_list]
  simp

theorem allOneWord_valid (k : ℕ) : ValidWord k (3 ^ k - 1) (allOneWord k) := by
  unfold ValidWord
  rw [allOneWord_list]
  simpa using validTuple_ones k 1 (by decide)

/-- The all-one tuple gives an actual atom of the arithmetic word law. -/
theorem arithmetic_mass_lower (k : ℕ) :
    (1 / 2 : ℝ) ^ k ≤ arithmeticMass k (3 ^ k - 1) := by
  classical
  have h := (arithmeticTerm_summable k (3 ^ k - 1)).le_tsum (allOneWord k)
    (fun w _ => arithmeticTerm_nonneg k (3 ^ k - 1) w)
  simpa only [arithmeticTerm, if_pos (allOneWord_valid k), allOneWord_length] using h

#print axioms validTuple_ones
#print axioms arithmetic_mass_lower

end CollatzCylinderPacking.Arithmetic
