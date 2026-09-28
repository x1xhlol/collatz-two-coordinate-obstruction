import CanonicalCylinderRecursion
import ActualWordDepth

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace CollatzCylinderPacking.Arithmetic

noncomputable def syracuseBlockOperator (s : ℝ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' a : ℕ, if ValidBlock (a + 1) N then
    (3 : ℝ) ^ s * ((2 : ℝ) ^ (-s)) ^ (a + 1) * f (inverseValue (a + 1) N) else 0

noncomputable def syracuseBlockIterate (s : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, N => syracuseBlockOperator s (syracuseBlockIterate s k) N

noncomputable def blockWordTerm (s : ℝ) (k N : ℕ) (w : GeometricWord k) : ℝ :=
  if ValidWord k N w then ((3 : ℝ) ^ s) ^ k * ((2 : ℝ) ^ (-s)) ^ wordLength k w else 0

theorem blockWordTerm_nonneg (s : ℝ) (k N : ℕ) (w : GeometricWord k) :
    0 ≤ blockWordTerm s k N w := by
  unfold blockWordTerm
  split_ifs <;> positivity

theorem blockWordTerm_summable {s : ℝ} (hs : 0 < s) (k N : ℕ) :
    Summable (blockWordTerm s k N) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  apply Summable.of_nonneg_of_le (blockWordTerm_nonneg s k N) _
    ((geometric_word_hasSum hr0 hr1 k).summable.mul_left (((3 : ℝ) ^ s) ^ k))
  intro w
  unfold blockWordTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem blockWordTerm_succ (s : ℝ) (k N a : ℕ) (w : GeometricWord k) :
    blockWordTerm s (k + 1) N (a, w) =
      if ValidBlock (a + 1) N then
        (3 : ℝ) ^ s * ((2 : ℝ) ^ (-s)) ^ (a + 1) *
          blockWordTerm s k (inverseValue (a + 1) N) w else 0 := by
  classical
  unfold blockWordTerm
  simp only [ValidWord, wordList, ValidTuple, wordLength]
  split_ifs <;> simp_all [pow_succ, pow_add]
  ring

/-- Every iterate of the manuscript's odd-block operator is the full
arithmetically valid geometric-word sum. -/
theorem syracuseBlockIterate_eq_word_sum {s : ℝ} (hs : 0 < s) (k N : ℕ) :
    syracuseBlockIterate s k N = ∑' w : GeometricWord k, blockWordTerm s k N w := by
  induction k generalizing N with
  | zero => simp [syracuseBlockIterate, blockWordTerm, GeometricWord,
      ValidWord, wordList, ValidTuple, wordLength]
  | succ k ih =>
    change syracuseBlockOperator s (syracuseBlockIterate s k) N =
      ∑' p : ℕ × GeometricWord k, blockWordTerm s (k + 1) N p
    rw [(blockWordTerm_summable hs (k + 1) N).tsum_prod]
    unfold syracuseBlockOperator
    apply tsum_congr
    intro a
    simp_rw [blockWordTerm_succ]
    by_cases ha : ValidBlock (a + 1) N
    · simp only [if_pos ha, ih, tsum_mul_left]
    · simp only [if_neg ha, tsum_zero]

theorem blockWordTerm_one (k N : ℕ) (w : GeometricWord k) :
    blockWordTerm 1 k N w = (3 : ℝ) ^ k * arithmeticTerm k N w := by
  classical
  unfold blockWordTerm arithmeticTerm
  simp only [Real.rpow_one, Real.rpow_neg_one]
  split_ifs <;> simp [one_div]

/-- Normalized canonical cylinders are precisely the s=1 odd-block iterates. -/
theorem canonicalRho_eq_syracuseBlockIterate {N : ℕ} (hN : 0 < N) (k : ℕ) :
    canonicalRho k N = syracuseBlockIterate 1 k N := by
  rw [syracuseBlockIterate_eq_word_sum (by norm_num : (0 : ℝ) < 1),
    canonicalRho_eq_arithmetic hN]
  simp only [blockWordTerm_one, arithmeticMass, tsum_mul_left]


theorem block_weight_rpow (s : ℝ) (k A : ℕ) :
    ((3 : ℝ) ^ k / (2 : ℝ) ^ A) ^ s =
      ((3 : ℝ) ^ s) ^ k * ((2 : ℝ) ^ (-s)) ^ A := by
  rw [Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_pow, div_eq_mul_inv]

theorem validBlock_iff_residue {N : ℕ} (hN : 0 < N) (a : ℕ) :
    ValidBlock (a + 1) N ↔ (2 ^ (a + 1) * N) % 3 = 1 := by
  have hp : 0 < 2 ^ (a + 1) * N := Nat.mul_pos (by positivity) hN
  unfold ValidBlock
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- The explicit positive-exponent formula for the manuscript's operator. -/
theorem syracuseBlockOperator_formula (s : ℝ) (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    syracuseBlockOperator s f N =
      ∑' a : ℕ, if (2 ^ (a + 1) * N) % 3 = 1 then
        ((3 : ℝ) / (2 : ℝ) ^ (a + 1)) ^ s * f ((2 ^ (a + 1) * N - 1) / 3) else 0 := by
  unfold syracuseBlockOperator
  apply tsum_congr
  intro a
  rw [validBlock_iff_residue hN, ← show
    ((3 : ℝ) / (2 : ℝ) ^ (a + 1)) ^ s =
      (3 : ℝ) ^ s * ((2 : ℝ) ^ (-s)) ^ (a + 1) by
        simpa only [pow_one] using block_weight_rpow s 1 (a + 1)]
  split_ifs <;> rfl

#print axioms syracuseBlockOperator_formula
#print axioms syracuseBlockIterate_eq_word_sum
#print axioms canonicalRho_eq_syracuseBlockIterate

end CollatzCylinderPacking.Arithmetic
