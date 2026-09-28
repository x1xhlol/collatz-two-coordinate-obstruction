/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import FormalConjectures.Wikipedia.CollatzConjecture
import Mathlib.Tactic

/-!
# Basic Collatz Target Interfaces

This file contains tiny aliases and proposition-level interfaces around the canonical
`FormalConjectures.Wikipedia.CollatzConjecture` target.
-/

open Function

namespace Erdos1135SecondScale

/-- Local abbreviation for the canonical Collatz step function. -/
abbrev collatzStep : ℕ → ℕ :=
  CollatzConjecture.collatzStep

/-- The proposition hidden by the public `type_of%` wrapper in `Target.lean`. -/
def collatzProp : Prop :=
  ∀ n : ℕ, n > 0 → ∃ m, collatzStep^[m] n = 1

lemma collatzProp_def :
    collatzProp = (∀ n : ℕ, n > 0 → ∃ m, collatzStep^[m] n = 1) :=
  rfl

end Erdos1135SecondScale
