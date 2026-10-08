import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace CollatzPassageAtoms

theorem cumulative_composition_card (L : ℕ) :
    (∑ n ∈ Finset.range (L + 1), Fintype.card (Composition n)) = 2 ^ L := by
  simp only [composition_card]
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel]
    omega

theorem bounded_composition_card (L : ℕ) :
    Fintype.card (Σ n : Fin (L + 1), Composition n.val) = 2 ^ L := by
  rw [Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun n => Fintype.card (Composition n))]
  exact cumulative_composition_card L

/-- Counting all possible positive valuation tuples of total cost at most L,
including the empty tuple, gives exactly the binary budget 2^L. -/
theorem finite_source_fiber_card_le (s : Finset ℕ) (word : ℕ → List ℕ) (L : ℕ)
    (hpos : ∀ q ∈ s, ∀ a ∈ word q, 0 < a)
    (hcost : ∀ q ∈ s, (word q).sum ≤ L)
    (hinj : Set.InjOn word (s : Set ℕ)) : s.card ≤ 2 ^ L := by
  let encode (q : s) : Σ n : Fin (L + 1), Composition n.val :=
    ⟨⟨(word q.val).sum, by have := hcost q.val q.property; omega⟩,
      ⟨word q.val, fun {a} ha => hpos q.val q.property a ha, rfl⟩⟩
  have he : Function.Injective encode := by
    intro q r hqr
    apply Subtype.ext
    apply hinj q.property r.property
    have heq := congrArg (fun c : Σ n : Fin (L + 1), Composition n.val => c.2.blocks) hqr
    exact heq
  have hc := Fintype.card_le_of_injective encode he
  simpa only [Fintype.card_coe, bounded_composition_card] using hc

end CollatzPassageAtoms
