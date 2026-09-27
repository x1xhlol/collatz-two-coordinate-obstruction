import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CollatzResearch

def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def ReachesOne (n : ℕ) : Prop := ∃ k : ℕ, step^[k] n = 1

def CollatzConjecture : Prop := ∀ n : ℕ, 0 < n → ReachesOne n

def Descends (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < step^[k] n ∧ step^[k] n < n

def UniversalDescent : Prop := ∀ n : ℕ, 1 < n → Descends n

theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  unfold step
  split_ifs with heven
  · omega
  · omega

theorem iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < step^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_pos ih

theorem reaches_one_of_reachable {n m k : ℕ}
    (hpath : step^[k] n = m) (hm : ReachesOne m) : ReachesOne n := by
  obtain ⟨j, hj⟩ := hm
  refine ⟨j + k, ?_⟩
  rw [Function.iterate_add_apply, hpath, hj]

theorem collatz_iff_universal_descent : CollatzConjecture ↔ UniversalDescent := by
  constructor
  · intro h n hn
    obtain ⟨k, hk⟩ := h n (by omega)
    exact ⟨k, by rw [hk]; omega, by rw [hk]; exact hn⟩
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hbase : n = 1
      · exact ⟨0, hbase⟩
      · obtain ⟨k, hkpos, hklt⟩ := h n (by omega)
        exact reaches_one_of_reachable rfl (ih (step^[k] n) hklt hkpos)

theorem step_even (m : ℕ) : step (2 * m) = m := by
  simp [step]

theorem step_odd (m : ℕ) : step (2 * m + 1) = 6 * m + 4 := by
  simp [step]
  ring

theorem two_steps_odd (m : ℕ) : step^[2] (2 * m + 1) = 3 * m + 2 := by
  change step (step (2 * m + 1)) = 3 * m + 2
  rw [step_odd]
  have he : 6 * m + 4 = 2 * (3 * m + 2) := by ring
  rw [he, step_even]

theorem power_two_steps (a m : ℕ) : step^[a] (2 ^ a * m) = m := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    have he : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by
      rw [pow_succ]
      ring
    rw [he, step_even, ih]

theorem odd_block_reachable {n a m : ℕ}
    (hodd : n % 2 ≠ 0) (hblock : 3 * n + 1 = 2 ^ a * m) :
    step^[a + 1] n = m := by
  rw [Function.iterate_succ_apply]
  simp only [step, hodd, if_false]
  rw [hblock, power_two_steps]

theorem collatz_of_rank (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1)) :
    CollatzConjecture := by
  have hmain : ∀ q n : ℕ, rank n = q → 0 < n → ReachesOne n := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ihq =>
      intro n
      induction n using Nat.strong_induction_on with
      | h n ihn =>
        intro hq hn
        by_cases hbase : n = 1
        · exact ⟨0, hbase⟩
        · by_cases he : n % 2 = 0
          · have hmpos : 0 < n / 2 := by omega
            have hform : n = 2 * (n / 2) := by omega
            have hmlt : n / 2 < n := by omega
            have hmrank : rank (n / 2) ≤ q := by
              calc
                rank (n / 2) ≤ rank (2 * (n / 2)) := heven (n / 2) hmpos
                _ = q := by rw [← hform, hq]
            have hm : ReachesOne (n / 2) := by
              rcases lt_or_eq_of_le hmrank with hs | hs
              · exact ihq (rank (n / 2)) hs (n / 2) rfl hmpos
              · exact ihn (n / 2) hmlt hs hmpos
            apply reaches_one_of_reachable (k := 1) (m := n / 2) _ hm
            simp [step, he]
          · have hmpos : 0 < n / 2 := by omega
            have hform : n = 2 * (n / 2) + 1 := by omega
            have hmrank : rank (3 * (n / 2) + 2) < q := by
              calc
                rank (3 * (n / 2) + 2) < rank (2 * (n / 2) + 1) :=
                  hodd (n / 2) hmpos
                _ = q := by rw [← hform, hq]
            have hm := ihq (rank (3 * (n / 2) + 2)) hmrank
              (3 * (n / 2) + 2) rfl (by omega)
            apply reaches_one_of_reachable (k := 2) (m := 3 * (n / 2) + 2) _ hm
            rw [hform, two_steps_odd]
            omega
  intro n hn
  exact hmain (rank n) n rfl hn

theorem even_descends {n : ℕ} (hn : 1 < n) (heven : n % 2 = 0) :
    Descends n := by
  refine ⟨1, ?_, ?_⟩
  · exact iterate_pos (by omega) 1
  · simp only [Function.iterate_one]
    simp only [step, heven, if_true]
    omega

theorem three_steps_of_four_mul_add_one (m : ℕ) :
    step^[3] (4 * m + 1) = 3 * m + 1 := by
  have h1 : step (4 * m + 1) = 12 * m + 4 := by
    unfold step
    have hm : (4 * m + 1) % 2 ≠ 0 := by omega
    rw [if_neg hm]
    ring
  have h2 : step (12 * m + 4) = 6 * m + 2 := by
    have he : 12 * m + 4 = 2 * (6 * m + 2) := by ring
    rw [he, step_even]
  have h3 : step (6 * m + 2) = 3 * m + 1 := by
    have he : 6 * m + 2 = 2 * (3 * m + 1) := by ring
    rw [he, step_even]
  change step (step (step (4 * m + 1))) = 3 * m + 1
  rw [h1, h2, h3]

theorem one_mod_four_descends {n : ℕ} (hn : 1 < n) (hmod : n % 4 = 1) :
    Descends n := by
  have hnform : n = 4 * (n / 4) + 1 := by omega
  refine ⟨3, iterate_pos (by omega) 3, ?_⟩
  rw [hnform, three_steps_of_four_mul_add_one]
  omega

theorem non_descending_is_three_mod_four {n : ℕ}
    (hn : 1 < n) (hno : ¬ Descends n) : n % 4 = 3 := by
  have hodd : n % 2 ≠ 0 := fun he => hno (even_descends hn he)
  have hnotone : n % 4 ≠ 1 := fun ho => hno (one_mod_four_descends hn ho)
  omega

theorem universal_descent_iff_three_mod_four :
    UniversalDescent ↔ ∀ n : ℕ, 1 < n → n % 4 = 3 → Descends n := by
  constructor
  · intro h n hn _
    exact h n hn
  · intro h n hn
    by_contra hno
    exact hno (h n hn (non_descending_is_three_mod_four hn hno))

theorem collatz_iff_three_mod_four_descent :
    CollatzConjecture ↔ ∀ n : ℕ, 1 < n → n % 4 = 3 → Descends n := by
  exact collatz_iff_universal_descent.trans universal_descent_iff_three_mod_four

#print axioms step_pos
#print axioms iterate_pos
#print axioms reaches_one_of_reachable
#print axioms collatz_iff_universal_descent
#print axioms step_even
#print axioms step_odd
#print axioms two_steps_odd
#print axioms power_two_steps
#print axioms odd_block_reachable
#print axioms collatz_of_rank
#print axioms even_descends
#print axioms three_steps_of_four_mul_add_one
#print axioms one_mod_four_descends
#print axioms non_descending_is_three_mod_four
#print axioms universal_descent_iff_three_mod_four
#print axioms collatz_iff_three_mod_four_descent

end CollatzResearch
