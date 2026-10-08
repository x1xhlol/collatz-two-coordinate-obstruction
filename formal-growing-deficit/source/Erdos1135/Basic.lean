import FormalConjectures.Wikipedia.CollatzConjecture
import Mathlib.Tactic

/-!
# Basic Collatz Target Interfaces

This file contains tiny aliases and proposition-level interfaces around the canonical
`FormalConjectures.Wikipedia.CollatzConjecture` target.
-/

open Function

namespace Erdos1135

/-- Local abbreviation for the canonical Collatz step function. -/
abbrev collatzStep : ℕ → ℕ :=
  CollatzConjecture.collatzStep

/-- The proposition hidden by the public `type_of%` wrapper in `Target.lean`. -/
def collatzProp : Prop :=
  ∀ n : ℕ, n > 0 → ∃ m, collatzStep^[m] n = 1

lemma collatzProp_def :
    collatzProp = (∀ n : ℕ, n > 0 → ∃ m, collatzStep^[m] n = 1) :=
  rfl

end Erdos1135
