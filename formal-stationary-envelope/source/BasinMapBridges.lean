import OptimalCylinderPacking

/-!
Elementary map bridges for the basin-density manuscript. The inclusion from
ordinary predecessors of 2N to shortcut predecessors of N also appears in
Lech Mazur, Positive Lower Density of Collatz Predecessors (2026), equation (1.3).
No external density theorem is assumed or proved in this module.
-/

set_option autoImplicit false

namespace CollatzBasinMapBridges

open CollatzCylinderPacking

def rawStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def rawIterate : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => rawIterate k (rawStep n)

theorem iterate_step (k n : ℕ) :
    iterate k (step n) = iterate (k + 1) n := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterate] using congrArg step ih

theorem raw_hit_double_implies_shortcut_hit (k n N : ℕ)
    (h : rawIterate k n = 2 * N) : ∃ j : ℕ, iterate j n = N := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero =>
      have hn : n = 2 * N := h
      subst n
      exact ⟨1, by simp [iterate, step]⟩
    | succ k =>
      by_cases hn : n % 2 = 0
      · have hs : rawStep n = step n := by simp [rawStep, step, hn]
        have hh : rawIterate k (step n) = 2 * N := by
          simpa only [rawIterate, hs] using h
        obtain ⟨j, hj⟩ := ih k (by omega) (step n) hh
        exact ⟨j + 1, by rw [← iterate_step]; exact hj⟩
      · have hn1 : n % 2 = 1 := by omega
        have hr : rawStep n = 3 * n + 1 := by simp [rawStep, hn]
        cases k with
        | zero =>
          have hh : 3 * n + 1 = 2 * N := by simpa [rawIterate, hr] using h
          exact ⟨1, by simp [iterate, step, hn]; omega⟩
        | succ k =>
          have he : rawStep n % 2 = 0 := by rw [hr]; omega
          have hs : rawStep (rawStep n) = step n := by
            calc
              rawStep (rawStep n) = rawStep n / 2 := if_pos he
              _ = step n := by simp only [hr, step, if_neg hn]
          have hh : rawIterate k (step n) = 2 * N := by
            simpa only [rawIterate, hs] using h
          obtain ⟨j, hj⟩ := ih k (by omega) (step n) hh
          exact ⟨j + 1, by rw [← iterate_step]; exact hj⟩

theorem even_of_step_divisible_by_three {n : ℕ}
    (h : step n % 3 = 0) : n % 2 = 0 := by
  by_contra hn
  have hn1 : n % 2 = 1 := by omega
  have hs := step_odd hn1
  omega

theorem hit_multiple_of_three_iff (k n N : ℕ) (hN : N % 3 = 0) :
    iterate k n = N ↔ n = 2 ^ k * N := by
  induction k generalizing n with
  | zero => simp [iterate]
  | succ k ih =>
    rw [← iterate_step, ih]
    constructor
    · intro h
      have hm : step n % 3 = 0 := by simp [h, Nat.mul_mod, hN]
      have he := even_of_step_divisible_by_three hm
      have hs := step_even he
      rw [h] at hs
      rw [pow_succ]
      nlinarith
    · intro h
      have hh : n = 2 * (2 ^ k * N) := by rw [h, pow_succ]; ring
      simp [hh, step]

#print axioms raw_hit_double_implies_shortcut_hit
#print axioms hit_multiple_of_three_iff

end CollatzBasinMapBridges
