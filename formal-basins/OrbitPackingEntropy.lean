import OrbitPackingParityCount
import FiniteBinomialTail

/-! Finite entropy bounds for the odd-step counts of actual shortcut starts. -/

set_option autoImplicit false

namespace CollatzOrbitPackingEntropy

open CollatzCylinderPacking CollatzOrbitPackingParityCount

theorem odd_count_chernoff_bound (k : ℕ) (ρ t : ℝ) (ht : 0 ≤ t) :
    (((Finset.range (2 ^ k)).filter
      (fun n => ρ * k < (oddCount k n : ℝ))).card : ℝ) ≤
      Real.exp ((k : ℝ) * Real.log (1 + Real.exp t) - t * (ρ * k)) := by
  rw [card_oddCount_filter k (fun j : ℕ => ρ * k < (j : ℝ))]
  simp only [Nat.cast_sum]
  exact CollatzCanonical.BinomialTail.chernoff_binomial_tail k ρ t ht

theorem odd_count_binary_entropy_bound (k : ℕ) (ρ : ℝ)
    (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) :
    (((Finset.range (2 ^ k)).filter
      (fun n => ρ * k < (oddCount k n : ℝ))).card : ℝ) ≤
      (2 : ℝ) ^ ((k : ℝ) *
        ((-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2)) := by
  rw [card_oddCount_filter k (fun j : ℕ => ρ * k < (j : ℝ))]
  simp only [Nat.cast_sum]
  exact CollatzCanonical.BinomialTail.binary_entropy_binomial_tail k ρ hρ hρ1

/-- The entropy bound for any collection of starts below `2^(k+1)`.
The factor two accounts for the two complete residue periods. -/
theorem subset_double_range_binary_entropy_bound {k : ℕ} {S : Finset ℕ}
    (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hS : S ⊆ Finset.range (2 * 2 ^ k))
    (hodd : ∀ n ∈ S, ρ * k < (oddCount k n : ℝ)) :
    (S.card : ℝ) ≤ 2 * (2 : ℝ) ^ ((k : ℝ) *
      ((-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2)) := by
  have hcard := card_subset_double_range_le (fun j : ℕ => ρ * k < (j : ℝ)) hS hodd
  have hreal : (S.card : ℝ) ≤ 2 *
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)),
        (k.choose j : ℝ) := by exact_mod_cast hcard
  exact hreal.trans (mul_le_mul_of_nonneg_left
    (CollatzCanonical.BinomialTail.binary_entropy_binomial_tail k ρ hρ hρ1)
    (by norm_num))

#print axioms odd_count_chernoff_bound
#print axioms odd_count_binary_entropy_bound
#print axioms subset_double_range_binary_entropy_bound

end CollatzOrbitPackingEntropy
