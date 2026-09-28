import AffineFamilySynchronization
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace CollatzPositiveProgression

open CollatzAffineSynchronization

def PatternSynchronizes (F : Finset ℕ) : Prop :=
  ∃ k a : ℕ, 0 < a ∧ ∀ n ∈ F, ∀ t : ℕ,
    iterate k (a + 2 ^ k * t + n) = iterate k (a + 2 ^ k * t)

theorem pattern_synchronizes_empty : PatternSynchronizes ∅ := by
  exact ⟨0, 1, by omega, by simp⟩

theorem pattern_synchronizes_insert (F : Finset ℕ) (n : ℕ)
    (h : PatternSynchronizes F) : PatternSynchronizes (insert n F) := by
  obtain ⟨k, a, ha, h⟩ := h
  obtain ⟨l, t₀, hs⟩ := synchronizes_all
    (oddCount k a) (iterate k a) (oddCount k (a + n)) (iterate k (a + n))
  refine ⟨k + l, a + 2 ^ k * t₀, by omega, ?_⟩
  intro m hm t
  have heq : (a + 2 ^ k * t₀) + 2 ^ (k + l) * t =
      a + 2 ^ k * (t₀ + 2 ^ l * t) := by
    rw [pow_add]
    ring
  rw [heq, iterate_add, iterate_add]
  rcases Finset.mem_insert.mp hm with rfl | hm
  · have hn : a + 2 ^ k * (t₀ + 2 ^ l * t) + m =
        (a + m) + 2 ^ k * (t₀ + 2 ^ l * t) := by omega
    rw [hn, iterate_progression, iterate_progression]
    exact (hs t).symm
  · rw [h m hm (t₀ + 2 ^ l * t)]

theorem pattern_synchronizes_all (F : Finset ℕ) : PatternSynchronizes F := by
  induction F using Finset.induction_on with
  | empty => exact pattern_synchronizes_empty
  | @insert n F _ ih => exact pattern_synchronizes_insert F n ih

theorem oddCount_eq_of_progression_equality (k a b : ℕ)
    (h : ∀ t : ℕ, iterate k (a + 2 ^ k * t) = iterate k (b + 2 ^ k * t)) :
    oddCount k a = oddCount k b := by
  have hzero : iterate k a = iterate k b := by simpa using h 0
  have hone := h 1
  rw [iterate_progression, iterate_progression, hzero] at hone
  have hp : (3 : ℕ) ^ oddCount k a = 3 ^ oddCount k b := by omega
  exact Nat.pow_right_injective (by omega : 2 ≤ (3 : ℕ)) hp

theorem every_finite_pattern_coalesces (F : Finset ℕ) :
    ∃ K R a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ n ∈ F, ∀ t : ℕ,
      iterate K (a + 2 ^ K * t + n) = b + 3 ^ R * t ∧
      oddCount K (a + 2 ^ K * t + n) = R := by
  obtain ⟨K, a, ha, h⟩ := pattern_synchronizes_all F
  refine ⟨K, oddCount K a, a, iterate K a, ha, iterate_positive K a ha, ?_⟩
  intro n hn t
  have heq : a + 2 ^ K * t + n = (a + n) + 2 ^ K * t := by omega
  have hR : oddCount K (a + n) = oddCount K a := by
    apply oddCount_eq_of_progression_equality K (a + n) a
    intro u
    have hu : (a + n) + 2 ^ K * u = a + 2 ^ K * u + n := by omega
    rw [hu]
    exact h n hn u
  constructor
  · rw [h n hn t, iterate_progression]
  · rw [heq, oddCount_progression, hR]

#print axioms every_finite_pattern_coalesces

end CollatzPositiveProgression
