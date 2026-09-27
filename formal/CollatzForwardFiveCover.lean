import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace CollatzResearch.ForwardFiveCover

open scoped BigOperators

/-- Each of the three carry intervals is reached within five normalized
multiplications by three. The witnesses use only nonnegative powers of two. -/
theorem five_stage_cover (x : ℝ) (hx₁ : 1 ≤ x) (hx₂ : x ≤ 2) (h : Fin 3) :
    ∃ j t : ℕ, j < 5 ∧
      (3 + (h.val : ℝ)) / 3 < (3 : ℝ) ^ j * x / (2 : ℝ) ^ t ∧
      (3 : ℝ) ^ j * x / (2 : ℝ) ^ t < (4 + (h.val : ℝ)) / 3 := by
  fin_cases h
  · by_cases h₀ : x < 32 / 27
    · refine ⟨2, 3, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₁ : x < 4 / 3
    · refine ⟨0, 0, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₂ : x < 128 / 81
    · refine ⟨3, 5, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₃ : x < 16 / 9
    · refine ⟨1, 2, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨4, 7, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
  · by_cases h₀ : x < 10 / 9
    · refine ⟨1, 1, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₁ : x < 320 / 243
    · refine ⟨4, 6, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₂ : x < 40 / 27
    · refine ⟨2, 3, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₃ : x < 5 / 3
    · refine ⟨0, 0, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₄ : x < 160 / 81
    · refine ⟨3, 5, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨1, 2, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
  · by_cases h₀ : x < 32 / 27
    · refine ⟨3, 4, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₁ : x < 4 / 3
    · refine ⟨1, 1, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₂ : x < 128 / 81
    · refine ⟨4, 6, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₃ : x < 16 / 9
    · refine ⟨2, 3, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    by_cases h₄ : x < 2
    · refine ⟨0, 0, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨3, 5, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith

/-- A block containing all three labels contributes at least the sum of their
nonnegative weights. -/
theorem block_sum_lower_bound (f : ℕ → Fin 3)
    (hcover : ∀ (k : ℕ) (h : Fin 3), ∃ j : ℕ, j < 5 ∧ f (k + j) = h)
    (δ : Fin 3 → ℝ) (hδ : ∀ h, 0 ≤ δ h) (k : ℕ) :
    δ 0 + δ 1 + δ 2 ≤ ∑ j ∈ Finset.range 5, δ (f (k + j)) := by
  obtain ⟨j₀, hj₀, h₀⟩ := hcover k 0
  obtain ⟨j₁, hj₁, h₁⟩ := hcover k 1
  obtain ⟨j₂, hj₂, h₂⟩ := hcover k 2
  have h₀₁ : j₀ ≠ j₁ := by
    intro heq
    have hc : (0 : Fin 3) = 1 :=
      h₀.symm.trans ((congrArg (fun j => f (k + j)) heq).trans h₁)
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  have h₀₂ : j₀ ≠ j₂ := by
    intro heq
    have hc : (0 : Fin 3) = 2 :=
      h₀.symm.trans ((congrArg (fun j => f (k + j)) heq).trans h₂)
    exact (by decide : (0 : Fin 3) ≠ 2) hc
  have h₁₂ : j₁ ≠ j₂ := by
    intro heq
    have hc : (1 : Fin 3) = 2 :=
      h₁.symm.trans ((congrArg (fun j => f (k + j)) heq).trans h₂)
    exact (by decide : (1 : Fin 3) ≠ 2) hc
  have hsubset : ({j₀, j₁, j₂} : Finset ℕ) ⊆ Finset.range 5 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact Finset.mem_range.mpr hj₀
    · exact Finset.mem_range.mpr hj₁
    · exact Finset.mem_range.mpr hj₂
  calc
    δ 0 + δ 1 + δ 2 = ∑ j ∈ ({j₀, j₁, j₂} : Finset ℕ), δ (f (k + j)) := by
      simp [h₀₁, h₀₂, h₁₂, h₀, h₁, h₂, add_assoc]
    _ ≤ ∑ j ∈ Finset.range 5, δ (f (k + j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j _ _ => hδ (f (k + j)))

/-- Disjoint five-stage blocks yield a uniform lower bound for every prefix. -/
theorem prefix_sum_lower_bound (f : ℕ → Fin 3)
    (hcover : ∀ (k : ℕ) (h : Fin 3), ∃ j : ℕ, j < 5 ∧ f (k + j) = h)
    (δ : Fin 3 → ℝ) (hδ : ∀ h, 0 ≤ δ h) (n : ℕ) :
    ((n / 5 : ℕ) : ℝ) * (δ 0 + δ 1 + δ 2) ≤
      ∑ j ∈ Finset.range n, δ (f j) := by
  have hblocks : ∀ m : ℕ, (m : ℝ) * (δ 0 + δ 1 + δ 2) ≤
      ∑ j ∈ Finset.range (5 * m), δ (f j) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hblock := block_sum_lower_bound f hcover δ hδ (5 * m)
        rw [Nat.mul_succ, Finset.sum_range_add]
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith
  exact (hblocks (n / 5)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.mul_div_le n 5))
      (fun j _ _ => hδ (f j)))

end CollatzResearch.ForwardFiveCover
