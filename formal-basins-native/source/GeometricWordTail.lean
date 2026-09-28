import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace CollatzCylinderPacking

/-- A k-tuple of positive exponents, represented by their nonnegative
predecessors. No admissibility restriction is imposed. -/
def GeometricWord : ℕ → Type
  | 0 => Unit
  | k + 1 => ℕ × GeometricWord k

def wordLength : (k : ℕ) → GeometricWord k → ℕ
  | 0, _ => 0
  | k + 1, (a, w) => a + 1 + wordLength k w

theorem geometric_word_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    HasSum (fun w : GeometricWord k => r ^ wordLength k w) ((r / (1 - r)) ^ k) := by
  have hs : HasSum (fun a : ℕ => r ^ (a + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  induction k with
  | zero =>
    simp [GeometricWord, wordLength]
  | succ k ih =>
    have hf : Summable (fun a : ℕ => ‖r ^ (a + 1)‖) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 _)] using hs.summable
    have hg : Summable (fun w : GeometricWord k => ‖r ^ wordLength k w‖) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 _)] using ih.summable
    have hprod : Summable (fun p : ℕ × GeometricWord k =>
        r ^ (p.1 + 1) * r ^ wordLength k p.2) :=
      summable_mul_of_summable_norm
        (f := fun a : ℕ => r ^ (a + 1))
        (g := fun w : GeometricWord k => r ^ wordLength k w) hf hg
    have hp : HasSum (fun p : ℕ × GeometricWord k =>
        r ^ (p.1 + 1) * r ^ wordLength k p.2)
        ((r / (1 - r)) * (r / (1 - r)) ^ k) := hs.mul ih hprod
    change HasSum (fun p : ℕ × GeometricWord k =>
      r ^ (p.1 + 1 + wordLength k p.2)) ((r / (1 - r)) ^ (k + 1))
    simpa only [pow_add, pow_succ'] using hp

theorem geometric_word_probability (k : ℕ) :
    HasSum (fun w : GeometricWord k => (1 / 2 : ℝ) ^ wordLength k w) 1 := by
  convert geometric_word_hasSum (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) k using 1
  norm_num

theorem geometric_word_tilted_mass (k : ℕ) :
    HasSum (fun w : GeometricWord k => (3 / 4 : ℝ) ^ wordLength k w) ((3 : ℝ) ^ k) := by
  convert geometric_word_hasSum (r := (3 / 4 : ℝ)) (by norm_num) (by norm_num) k using 1
  norm_num

noncomputable def geometricTailTerm (k : ℕ) (w : GeometricWord k) : ℝ :=
  if 5 * k ≤ wordLength k w then (1 / 2 : ℝ) ^ wordLength k w else 0

theorem geometricTailTerm_nonneg (k : ℕ) (w : GeometricWord k) :
    0 ≤ geometricTailTerm k w := by
  unfold geometricTailTerm
  split_ifs <;> positivity

theorem geometric_tail_summable (k : ℕ) : Summable (geometricTailTerm k) := by
  apply Summable.of_nonneg_of_le (geometricTailTerm_nonneg k) _
    (geometric_word_probability k).summable
  intro w
  unfold geometricTailTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem geometric_tail_pointwise (k : ℕ) (w : GeometricWord k) :
    geometricTailTerm k w ≤
      (2 / 3 : ℝ) ^ (5 * k) * (3 / 4 : ℝ) ^ wordLength k w := by
  unfold geometricTailTerm
  split_ifs with h
  · calc
      (1 / 2 : ℝ) ^ wordLength k w =
          (2 / 3 : ℝ) ^ wordLength k w * (3 / 4 : ℝ) ^ wordLength k w := by
        rw [← mul_pow]
        norm_num
      _ ≤ (2 / 3 : ℝ) ^ (5 * k) * (3 / 4 : ℝ) ^ wordLength k w :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) (by positivity)
  · positivity

/-- The complete infinite geometric tail, with no cylinder expansion assumed. -/
theorem geometric_tail_bound (k : ℕ) :
    (∑' w : GeometricWord k, geometricTailTerm k w) ≤ (32 / 81 : ℝ) ^ k := by
  have ht := (geometric_word_tilted_mass k).mul_left ((2 / 3 : ℝ) ^ (5 * k))
  calc
    (∑' w : GeometricWord k, geometricTailTerm k w) ≤
        ∑' w : GeometricWord k,
          (2 / 3 : ℝ) ^ (5 * k) * (3 / 4 : ℝ) ^ wordLength k w :=
      Summable.tsum_le_tsum (geometric_tail_pointwise k)
        (geometric_tail_summable k) ht.summable
    _ = (2 / 3 : ℝ) ^ (5 * k) * (3 : ℝ) ^ k := ht.tsum_eq
    _ = (32 / 81 : ℝ) ^ k := by
      rw [pow_mul, ← mul_pow]
      norm_num

theorem geometric_tail_le_half_pow (k : ℕ) :
    (∑' w : GeometricWord k, geometricTailTerm k w) ≤ (1 / 2 : ℝ) ^ k := by
  exact (geometric_tail_bound k).trans
    (pow_le_pow_left₀ (by norm_num) (by norm_num) k)

#print axioms geometric_word_hasSum
#print axioms geometric_tail_bound
#print axioms geometric_tail_le_half_pow

end CollatzCylinderPacking
