import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Push

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed

theorem no_return_or_no_return_of_same_successor {α : Type*} {f : α → α} {r s : α}
    (hne : r ≠ s) (hsame : f r = f s) :
    (∀ k : ℕ, 0 < k → (f^[k]) r ≠ r) ∨
      (∀ k : ℕ, 0 < k → (f^[k]) s ≠ s) := by
  classical
  by_cases hr : ∀ k : ℕ, 0 < k → (f^[k]) r ≠ r
  · exact Or.inl hr
  · right
    push Not at hr
    obtain ⟨m, hm, hmr⟩ := hr
    intro n hn hns
    exact hne ((show Function.IsPeriodicPt f m r from hmr).eq_of_apply_eq
      (show Function.IsPeriodicPt f n s from hns) hm hn hsame)

#print axioms no_return_or_no_return_of_same_successor

end CollatzCanonical.BoundedInverseSeed
