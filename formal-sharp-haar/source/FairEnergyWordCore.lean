import FiniteCylinderResidueLaw
import ArithmeticWordFibers

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

noncomputable def wordTranslation (k : ℕ) (w : GeometricWord k) : ℝ :=
  (affineNumerator (wordList k w) : ℝ) / (3 : ℝ) ^ k

noncomputable def biasedWordWeight (k : ℕ) (w : GeometricWord k) : ℝ :=
  (3 : ℝ) ^ k * (1 / 4 : ℝ) ^ wordLength k w

noncomputable def cubicMomentTerm (k : ℕ) (w : GeometricWord k) : ℝ :=
  biasedWordWeight k w * (wordLength k w : ℝ) ^ 3 * (1 + wordTranslation k w)

theorem wordTranslation_nonneg (k : ℕ) (w : GeometricWord k) :
    0 ≤ wordTranslation k w := by
  unfold wordTranslation
  positivity

theorem biasedWordWeight_nonneg (k : ℕ) (w : GeometricWord k) :
    0 ≤ biasedWordWeight k w := by
  unfold biasedWordWeight
  positivity

theorem cubicMomentTerm_nonneg (k : ℕ) (w : GeometricWord k) :
    0 ≤ cubicMomentTerm k w := by
  unfold cubicMomentTerm
  exact mul_nonneg
    (mul_nonneg (biasedWordWeight_nonneg k w) (by positivity))
    (by linarith [wordTranslation_nonneg k w])

theorem wordTranslation_zero (w : GeometricWord 0) : wordTranslation 0 w = 0 := by
  simp [wordTranslation, wordList, affineNumerator]

theorem biasedWordWeight_zero (w : GeometricWord 0) : biasedWordWeight 0 w = 1 := by
  simp [biasedWordWeight, wordLength]

theorem wordTranslation_succ (k a : ℕ) (w : GeometricWord k) :
    wordTranslation (k + 1) (a, w) = wordTranslation k w +
      (1 / 3 : ℝ) * ((2 : ℝ) ^ wordLength k w / (3 : ℝ) ^ k) := by
  simp only [wordTranslation, wordList, affineNumerator, wordList_sum,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp
  ring

theorem biasedWordWeight_succ (k a : ℕ) (w : GeometricWord k) :
    biasedWordWeight (k + 1) (a, w) =
      (3 * (1 / 4 : ℝ) ^ (a + 1)) * biasedWordWeight k w := by
  simp only [biasedWordWeight, wordLength, pow_add, pow_succ]
  ring

end CollatzCylinderPacking.Arithmetic.FairEnergy
