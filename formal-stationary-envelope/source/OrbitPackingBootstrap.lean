import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
A uniform strong-induction bootstrap for the counting recurrence in the
orbit-packing lemma. The recurrence, the smaller argument, and the contraction
of its weight are explicit hypotheses. The constant depends only on the
weight, threshold, and error coefficient, not on the indexed counting function.
-/

set_option autoImplicit false

namespace CollatzOrbitPackingBootstrap

open scoped BigOperators

noncomputable def bootstrapConstant (w : ℕ → ℝ) (N : ℕ) (C : ℝ) : ℝ :=
  max (2 * C) (∑ n ∈ Finset.range N, (n : ℝ) / w n)

theorem bound_of_smaller_argument_half_budget
    (A w : ℕ → ℝ) (next : ℕ → ℕ) (N : ℕ) (C K : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hK : 0 ≤ K) (hbudget : 2 * C ≤ K)
    (hbase : ∀ n, n < N → A n ≤ K * w n)
    (hnext : ∀ n, N ≤ n → next n < n)
    (hhalf : ∀ n, N ≤ n → w (next n) ≤ w n / 2)
    (hrec : ∀ n, N ≤ n → A n ≤ A (next n) + C * w n) :
    ∀ n, A n ≤ K * w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · exact hbase n hn
    · have hN : N ≤ n := Nat.le_of_not_gt hn
      calc
        A n ≤ A (next n) + C * w n := hrec n hN
        _ ≤ K * w (next n) + C * w n :=
          add_le_add (ih (next n) (hnext n hN)) le_rfl
        _ ≤ K * (w n / 2) + C * w n :=
          add_le_add (mul_le_mul_of_nonneg_left (hhalf n hN) hK) le_rfl
        _ = (K / 2 + C) * w n := by ring
        _ ≤ K * w n :=
          mul_le_mul_of_nonneg_right (by linarith) (hw n)

theorem bootstrapConstant_nonneg
    (w : ℕ → ℝ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ bootstrapConstant w N C := by
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC).trans (le_max_left _ _)

theorem initial_count_le_bootstrapConstant
    (w : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hwpos : ∀ n, 0 < n → 0 < w n)
    (hC : 0 ≤ C) (n : ℕ) (hn : n < N) :
    (n : ℝ) ≤ bootstrapConstant w N C * w n := by
  by_cases hn0 : n = 0
  · subst n
    simpa using mul_nonneg (bootstrapConstant_nonneg w N C hC) (hw 0)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hsingle : (n : ℝ) / w n ≤ ∑ j ∈ Finset.range N, (j : ℝ) / w j := by
      exact Finset.single_le_sum
        (fun j _ => div_nonneg (Nat.cast_nonneg j) (hw j))
        (Finset.mem_range.mpr hn)
    exact (div_le_iff₀ (hwpos n hnpos)).mp
      (hsingle.trans (le_max_right _ _))

/-- A single constant controls an arbitrary family of counting functions.
Only the elementary bound `A i n ≤ n` is needed in the finite initial range. -/
theorem uniform_counting_bootstrap
    {ι : Type*} (A : ι → ℕ → ℝ) (w : ℕ → ℝ)
    (next : ι → ℕ → ℕ) (N : ℕ) (C : ℝ)
    (hw : ∀ n, 0 ≤ w n) (hwpos : ∀ n, 0 < n → 0 < w n)
    (hC : 0 ≤ C)
    (hbase : ∀ i n, n < N → A i n ≤ (n : ℝ))
    (hnext : ∀ i n, N ≤ n → next i n < n)
    (hhalf : ∀ i n, N ≤ n → w (next i n) ≤ w n / 2)
    (hrec : ∀ i n, N ≤ n → A i n ≤ A i (next i n) + C * w n) :
    ∀ i n, A i n ≤ bootstrapConstant w N C * w n := by
  intro i
  apply bound_of_smaller_argument_half_budget (A i) w (next i) N C
    (bootstrapConstant w N C) hw (bootstrapConstant_nonneg w N C hC)
    (le_max_left _ _)
  · intro n hn
    exact (hbase i n hn).trans (initial_count_le_bootstrapConstant w N C hw hwpos hC n hn)
  · exact hnext i
  · exact hhalf i
  · exact hrec i

/-- Power-weight specialization. The same `K` works for the whole family;
the recurrence does not assume any of the bounds in the conclusion. -/
theorem uniform_power_bound_of_counting_recursion
    {ι : Type*} (A : ι → ℕ → ℝ) (next : ι → ℕ → ℕ)
    (N : ℕ) (b C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ i n, n < N → A i n ≤ (n : ℝ))
    (hnext : ∀ i n, N ≤ n → next i n < n)
    (hhalf : ∀ i n, N ≤ n → ((next i n : ℕ) : ℝ) ^ b ≤ (n : ℝ) ^ b / 2)
    (hrec : ∀ i n, N ≤ n → A i n ≤ A i (next i n) + C * (n : ℝ) ^ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i n, A i n ≤ K * (n : ℝ) ^ b := by
  let w : ℕ → ℝ := fun n => (n : ℝ) ^ b
  have hw : ∀ n, 0 ≤ w n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) b
  have hwpos : ∀ n, 0 < n → 0 < w n := by
    intro n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) b
  exact ⟨bootstrapConstant w N C, bootstrapConstant_nonneg w N C hC,
    uniform_counting_bootstrap A w next N C hw hwpos hC hbase hnext hhalf hrec⟩

#print axioms bound_of_smaller_argument_half_budget
#print axioms uniform_counting_bootstrap
#print axioms uniform_power_bound_of_counting_recursion

end CollatzOrbitPackingBootstrap
