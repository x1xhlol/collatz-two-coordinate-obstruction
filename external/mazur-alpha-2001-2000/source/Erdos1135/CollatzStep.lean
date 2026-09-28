import Erdos1135.Basic

/-!
# Basic Facts About `collatzStep`

This file records rewrite-oriented facts about the canonical Collatz step.
-/

namespace Erdos1135

lemma collatzStep_eq_div_two_of_even {n : ℕ} (hn : Even n) :
    collatzStep n = n / 2 := by
  simp [collatzStep, CollatzConjecture.collatzStep, hn]

lemma collatzStep_eq_three_mul_add_one_of_not_even {n : ℕ} (hn : ¬ Even n) :
    collatzStep n = 3 * n + 1 := by
  simp [collatzStep, CollatzConjecture.collatzStep, hn]

lemma collatzStep_zero : collatzStep 0 = 0 := by
  norm_num [collatzStep, CollatzConjecture.collatzStep]

lemma collatzStep_one : collatzStep 1 = 4 := by
  norm_num [collatzStep, CollatzConjecture.collatzStep]

lemma collatzStep_two : collatzStep 2 = 1 := by
  norm_num [collatzStep, CollatzConjecture.collatzStep]

lemma collatzStep_four : collatzStep 4 = 2 := by
  norm_num [collatzStep, CollatzConjecture.collatzStep]

end Erdos1135
