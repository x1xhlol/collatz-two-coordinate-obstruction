import Erdos1135.Iterate

/-!
# Orbit Predicates

Reusable predicates for reachability along Collatz iterates.
-/

namespace Erdos1135

/-- `Reaches a b` means the Collatz orbit starting at `a` reaches `b`. -/
def Reaches (a b : ℕ) : Prop :=
  ∃ m, collatzStep^[m] a = b

lemma reaches_refl (n : ℕ) : Reaches n n :=
  ⟨0, rfl⟩

lemma reaches_of_step_eq {a b : ℕ} (h : collatzStep a = b) :
    Reaches a b :=
  ⟨1, by simpa [iterate_collatzStep_succ_apply'] using h⟩

lemma reaches_trans {a b c : ℕ} (hab : Reaches a b) (hbc : Reaches b c) :
    Reaches a c := by
  rcases hab with ⟨m, hm⟩
  rcases hbc with ⟨n, hn⟩
  refine ⟨n + m, ?_⟩
  rw [iterate_collatzStep_add_apply, hm, hn]

lemma Reaches.trans {a b c : ℕ} (hab : Reaches a b) (hbc : Reaches b c) :
    Reaches a c :=
  reaches_trans hab hbc

lemma reaches_step (n : ℕ) :
    Reaches n (collatzStep n) :=
  reaches_of_step_eq rfl

lemma Reaches.step (n : ℕ) :
    Reaches n (collatzStep n) :=
  reaches_step n

lemma reaches_of_reaches_step {a b : ℕ} (h : Reaches (collatzStep a) b) :
    Reaches a b := by
  rcases h with ⟨m, hm⟩
  refine ⟨m.succ, ?_⟩
  rw [iterate_collatzStep_succ_apply]
  exact hm

lemma Reaches.step_left {a b : ℕ} (h : Reaches (collatzStep a) b) :
    Reaches a b :=
  reaches_of_reaches_step h

lemma reaches_step_right {a b : ℕ} (h : Reaches a b) :
    Reaches a (collatzStep b) :=
  reaches_trans h (reaches_step b)

lemma Reaches.step_right {a b : ℕ} (h : Reaches a b) :
    Reaches a (collatzStep b) :=
  reaches_step_right h

end Erdos1135
