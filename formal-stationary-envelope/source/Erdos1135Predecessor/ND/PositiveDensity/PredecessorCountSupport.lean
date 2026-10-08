/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Terras.Density.NaturalDensity

namespace Erdos1135Predecessor.Terras

theorem natCount_le (s : Set ℕ) (N : ℕ) : natCount s N ≤ N := by
  unfold natCount
  exact @Nat.count_le (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s)) N

theorem natCount_union_of_disjoint {s t : Set ℕ} (hdisj : Disjoint s t) (N : ℕ) :
    natCount (s ∪ t) N = natCount s N + natCount t N := by
  classical
  induction N with
  | zero => simp [natCount]
  | succ N ih =>
      unfold natCount at ih ⊢
      repeat rw [Nat.count_succ]
      rw [ih]
      have hnot : ¬(N ∈ s ∧ N ∈ t) := by
        intro h
        exact Set.disjoint_left.mp hdisj h.1 h.2
      by_cases hs : N ∈ s <;> by_cases ht : N ∈ t
      · exact (hnot ⟨hs, ht⟩).elim
      · simp [hs, ht, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [hs, ht, Nat.add_assoc]
      · simp [hs, ht]

end Erdos1135Predecessor.Terras
