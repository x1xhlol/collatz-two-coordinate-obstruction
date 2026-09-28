import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace CollatzPositiveProgression

def step (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

def iterate : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => iterate k (step x)

def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => x % 2 + oddCount k (step x)

theorem step_double (x : ℕ) : step (2 * x) = x := by
  simp [step]

theorem two_steps_one (x y : ℕ) (h : 3 * x + 1 = 4 * y) :
    step (step x) = y ∧ x % 2 + step x % 2 = 1 := by
  simp only [step]
  split_ifs <;> omega

theorem two_steps_two (x y : ℕ) (h : 3 * x + 2 = 4 * y) :
    step (step x) = y ∧ x % 2 + step x % 2 = 1 := by
  simp only [step]
  split_ifs <;> omega

theorem iterate_two (k x : ℕ) :
    iterate (k + 2) x = iterate k (step (step x)) := by
  rfl

theorem oddCount_two (k x : ℕ) :
    oddCount (k + 2) x = (x % 2 + step x % 2) + oddCount k (step (step x)) := by
  simp only [oddCount]
  omega

def Coalesces (n : ℕ) : Prop :=
  ∃ k a : ℕ, 0 < a ∧ ∀ t : ℕ,
    iterate k (a + 2 ^ k * t) = iterate k (a + 2 ^ k * t + n) ∧
    oddCount k (a + 2 ^ k * t) = oddCount k (a + 2 ^ k * t + n)

theorem coalesces_zero : Coalesces 0 := by
  exact ⟨0, 1, by omega, fun _ => by simp⟩

theorem coalesces_one : Coalesces 1 := by
  refine ⟨3, 4, by omega, ?_⟩
  intro t
  have h1 : step (4 + 8 * t) = 2 + 4 * t := by simp only [step]; split_ifs <;> omega
  have h2 : step (2 + 4 * t) = 1 + 2 * t := by simp only [step]; split_ifs <;> omega
  have h3 : step (1 + 2 * t) = 2 + 3 * t := by simp only [step]; split_ifs <;> omega
  have h4 : step (5 + 8 * t) = 8 + 12 * t := by simp only [step]; split_ifs <;> omega
  have h5 : step (8 + 12 * t) = 4 + 6 * t := by simp only [step]; split_ifs <;> omega
  have h6 : step (4 + 6 * t) = 2 + 3 * t := by simp only [step]; split_ifs <;> omega
  norm_num only [show (2 : ℕ) ^ 3 = 8 by norm_num]
  have hshift : 4 + 8 * t + 1 = 5 + 8 * t := by omega
  rw [hshift]
  simp only [iterate, oddCount, h1, h2, h3, h4, h5, h6]
  constructor
  · trivial
  · omega

theorem coalesces_double (n : ℕ) (h : Coalesces n) : Coalesces (2 * n) := by
  obtain ⟨k, a, ha, h⟩ := h
  refine ⟨k + 1, 2 * a, by omega, ?_⟩
  intro t
  have hp : 2 * a + 2 ^ (k + 1) * t = 2 * (a + 2 ^ k * t) := by
    rw [pow_succ]
    ring
  have hq : 2 * a + 2 ^ (k + 1) * t + 2 * n = 2 * (a + 2 ^ k * t + n) := by
    rw [pow_succ]
    ring
  rw [hq, hp]
  simp only [iterate, oddCount, step_double]
  simpa using h t

theorem two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with ih | ih <;> simp [ih]

theorem positive_lift (k a c : ℕ) (ha : 0 < a) (hc : c = 1 ∨ c = 2) :
    ∃ x s : ℕ, 0 < x ∧ 3 * x + c = 4 * (a + 2 ^ k * s) := by
  have hmod := two_pow_mod_three k
  have hres : ∃ s : ℕ, s ≤ 2 ∧ (4 * (a + 2 ^ k * s) - c) % 3 = 0 := by
    rcases hc with rfl | rfl <;> rcases hmod with hmod | hmod
    all_goals
      have ha3 := Nat.mod_lt a (by omega : 0 < 3)
      have h : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      rcases h with h | h | h
      all_goals first
        | exact ⟨0, by omega, by omega⟩
        | exact ⟨1, by omega, by omega⟩
        | exact ⟨2, by omega, by omega⟩
  obtain ⟨s, _, hs⟩ := hres
  refine ⟨(4 * (a + 2 ^ k * s) - c) / 3, s, ?_, ?_⟩
  · rcases hc with rfl | rfl <;> omega
  · rcases hc with rfl | rfl <;> omega

theorem two_steps (x y c : ℕ) (hc : c = 1 ∨ c = 2)
    (h : 3 * x + c = 4 * y) :
    step (step x) = y ∧ x % 2 + step x % 2 = 1 := by
  rcases hc with rfl | rfl
  · exact two_steps_one x y h
  · exact two_steps_two x y h

theorem coalesces_step (n m c d : ℕ)
    (hc : c = 1 ∨ c = 2) (hd : d = 1 ∨ d = 2)
    (hgap : 3 * n + d = 4 * m + c) (h : Coalesces m) : Coalesces n := by
  obtain ⟨k, a, ha, h⟩ := h
  obtain ⟨x, s, hx, hbase⟩ := positive_lift k a c ha hc
  refine ⟨k + 2, x, hx, ?_⟩
  intro t
  let y := a + 2 ^ k * (s + 3 * t)
  have hleft : 3 * (x + 2 ^ (k + 2) * t) + c = 4 * y := by
    dsimp [y]
    rw [pow_add]
    norm_num
    nlinarith [hbase]
  have hright : 3 * (x + 2 ^ (k + 2) * t + n) + d = 4 * (y + m) := by
    omega
  obtain ⟨hl, hcl⟩ := two_steps _ _ c hc hleft
  obtain ⟨hr, hcr⟩ := two_steps _ _ d hd hright
  rw [iterate_two, iterate_two, oddCount_two, oddCount_two, hl, hr, hcl, hcr]
  obtain ⟨hi, ho⟩ := h (s + 3 * t)
  exact ⟨hi, congrArg (1 + ·) ho⟩

theorem coalesces_all (n : ℕ) : Coalesces n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      exact coalesces_zero
    by_cases hone : n = 1
    · subst n
      exact coalesces_one
    by_cases heven : n % 2 = 0
    · have hlt : n / 2 < n := by omega
      have heq : 2 * (n / 2) = n := by omega
      simpa only [heq] using coalesces_double (n / 2) (ih (n / 2) hlt)
    by_cases hmod : n % 4 = 1
    · let m := (3 * n + 1) / 4
      have hlt : m < n := by dsimp [m]; omega
      have hnat : 3 * n + 2 = 4 * m + 1 := by dsimp [m]; omega
      exact coalesces_step n m 1 2 (by omega) (by omega) hnat (ih m hlt)
    · have hmod3 : n % 4 = 3 := by omega
      let m := (3 * n - 1) / 4
      have hlt : m < n := by dsimp [m]; omega
      have hnat : 3 * n + 1 = 4 * m + 2 := by dsimp [m]; omega
      exact coalesces_step n m 2 1 (by omega) (by omega) hnat (ih m hlt)

theorem every_gap_has_a_positive_coalescing_progression (n : ℕ) :
    ∃ k a : ℕ, 0 < a ∧ ∀ t : ℕ,
      iterate k (a + 2 ^ k * t) = iterate k (a + 2 ^ k * t + n) ∧
      oddCount k (a + 2 ^ k * t) = oddCount k (a + 2 ^ k * t + n) :=
  coalesces_all n

#print axioms every_gap_has_a_positive_coalescing_progression

end CollatzPositiveProgression
