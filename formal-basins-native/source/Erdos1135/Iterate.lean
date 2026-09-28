import Erdos1135.CollatzStep

/-!
# Iterate Interfaces

Small wrappers around `Function.iterate` specialized to the canonical Collatz step.
-/

open Function

namespace Erdos1135

lemma iterate_collatzStep_zero_apply (n : ℕ) :
    collatzStep^[0] n = n :=
  rfl

lemma iterate_collatzStep_one_apply (n : ℕ) :
    collatzStep^[1] n = collatzStep n := by
  rw [Function.iterate_one]

lemma iterate_collatzStep_succ_apply (m n : ℕ) :
    collatzStep^[m.succ] n = collatzStep^[m] (collatzStep n) := by
  rw [Function.iterate_succ_apply]

lemma iterate_collatzStep_succ_apply' (m n : ℕ) :
    collatzStep^[m.succ] n = collatzStep (collatzStep^[m] n) := by
  rw [Function.iterate_succ_apply']

lemma iterate_collatzStep_add_apply (m n a : ℕ) :
    collatzStep^[m + n] a = collatzStep^[m] (collatzStep^[n] a) := by
  rw [Function.iterate_add_apply]

end Erdos1135
