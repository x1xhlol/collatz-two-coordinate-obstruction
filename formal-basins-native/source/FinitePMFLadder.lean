import Erdos1135.Tao.Probability.FullL1
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace CollatzClockAudit
open Erdos1135.Tao

universe u

/-- Marginal transport across a finite ladder may change carriers at every
level. Deterministic maps contract full L1, so adjacent errors add. -/
theorem finite_pmf_ladder_tv_le (A : ℕ → Type u) [∀ i, Fintype (A i)]
    (f : ∀ i, A (i + 1) → A i) (μ ν : ∀ i, PMF (A i)) (err : ℕ → ℝ)
    (j : ℕ) (htop : μ j = ν j)
    (hμ : ∀ i < j, μ i = (μ (i + 1)).map (f i))
    (hν : ∀ i < j, taoTV ((ν (i + 1)).map (f i)) (ν i) ≤ err i)
    (i : ℕ) (hij : i ≤ j) :
    taoTV (μ i) (ν i) ≤ ∑ r ∈ Finset.Ico i j, err r := by
  refine Nat.decreasingInduction (motive := fun i _ =>
    taoTV (μ i) (ν i) ≤ ∑ r ∈ Finset.Ico i j, err r) ?_ ?_ hij
  · intro k hk ih
    rw [hμ k hk]
    calc
      taoTV ((μ (k + 1)).map (f k)) (ν k) ≤
          taoTV ((μ (k + 1)).map (f k)) ((ν (k + 1)).map (f k)) +
            taoTV ((ν (k + 1)).map (f k)) (ν k) := taoTV_triangle _ _ _
      _ ≤ taoTV (μ (k + 1)) (ν (k + 1)) + err k :=
        add_le_add (taoTV_map_le _ _ _) (hν k hk)
      _ ≤ (∑ r ∈ Finset.Ico (k + 1) j, err r) + err k := add_le_add ih le_rfl
      _ = ∑ r ∈ Finset.Ico k j, err r := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hk]
        ring
  · simp [htop, taoTV_self]

theorem finite_pmf_ladder_event_le (A : ℕ → Type u) [∀ i, Fintype (A i)]
    (f : ∀ i, A (i + 1) → A i) (μ ν : ∀ i, PMF (A i)) (err : ℕ → ℝ)
    (j : ℕ) (htop : μ j = ν j)
    (hμ : ∀ i < j, μ i = (μ (i + 1)).map (f i))
    (hν : ∀ i < j, taoTV ((ν (i + 1)).map (f i)) (ν i) ≤ err i)
    (i : ℕ) (hij : i ≤ j) (E : Set (A i)) {δ : ℝ}
    (hE : pmfProb (ν i) E ≤ δ) :
    pmfProb (μ i) E ≤ δ + ∑ r ∈ Finset.Ico i j, err r := by
  have htv := finite_pmf_ladder_tv_le A f μ ν err j htop hμ hν i hij
  have hp := pmfProb_sub_taoTV_le_pmfProb (μ i) (ν i) E
  linarith

end CollatzClockAudit
