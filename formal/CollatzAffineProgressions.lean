import PositiveProgressionCoalescence

set_option autoImplicit false

namespace CollatzPositiveProgression

theorem step_add_even (a t : ℕ) :
    step (a + 2 * t) = step a + 3 ^ (a % 2) * t := by
  have hm : (a + 2 * t) % 2 = a % 2 := by omega
  by_cases he : a % 2 = 0
  · simp only [step, hm, he, if_pos, pow_zero, one_mul]
    omega
  · have ho : a % 2 = 1 := by omega
    simp only [step, hm, ho, Nat.one_ne_zero, if_false, pow_one]
    omega

theorem iterate_oddCount_progression (k a t : ℕ) :
    iterate k (a + 2 ^ k * t) = iterate k a + 3 ^ oddCount k a * t ∧
    oddCount k (a + 2 ^ k * t) = oddCount k a := by
  induction k generalizing a t with
  | zero => simp [iterate, oddCount]
  | succ k ih =>
    have hp : a + 2 ^ (k + 1) * t = a + 2 * (2 ^ k * t) := by
      rw [pow_succ]
      ring
    have hm : (a + 2 ^ (k + 1) * t) % 2 = a % 2 := by
      rw [hp]
      omega
    have hs : step (a + 2 ^ (k + 1) * t) =
        step a + 2 ^ k * (3 ^ (a % 2) * t) := by
      rw [hp, step_add_even]
      ring
    obtain ⟨hi, ho⟩ := ih (step a) (3 ^ (a % 2) * t)
    simp only [iterate, oddCount, hm, hs, hi, ho]
    constructor
    · rw [pow_add]
      ring
    · trivial

theorem iterate_progression (k a t : ℕ) :
    iterate k (a + 2 ^ k * t) = iterate k a + 3 ^ oddCount k a * t :=
  (iterate_oddCount_progression k a t).1

theorem oddCount_progression (k a t : ℕ) :
    oddCount k (a + 2 ^ k * t) = oddCount k a :=
  (iterate_oddCount_progression k a t).2

theorem iterate_add (k l a : ℕ) :
    iterate (k + l) a = iterate l (iterate k a) := by
  induction k generalizing a with
  | zero => simp [iterate]
  | succ k ih => simpa only [Nat.succ_add, iterate] using ih (step a)

theorem oddCount_add (k l a : ℕ) :
    oddCount (k + l) a = oddCount k a + oddCount l (iterate k a) := by
  induction k generalizing a with
  | zero => simp [oddCount, iterate]
  | succ k ih =>
    simp only [Nat.succ_add, oddCount, iterate, ih]
    omega

theorem step_positive (a : ℕ) (ha : 0 < a) : 0 < step a := by
  simp only [step]
  split_ifs <;> omega

theorem iterate_positive (k a : ℕ) (ha : 0 < a) : 0 < iterate k a := by
  induction k generalizing a with
  | zero => exact ha
  | succ k ih => exact ih (step a) (step_positive a ha)

#print axioms iterate_oddCount_progression

end CollatzPositiveProgression
