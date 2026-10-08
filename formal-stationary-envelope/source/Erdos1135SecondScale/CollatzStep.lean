/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Basic

/-!
# Basic Facts About `collatzStep`

This file records rewrite-oriented facts about the canonical Collatz step.
-/

namespace Erdos1135SecondScale

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

end Erdos1135SecondScale
