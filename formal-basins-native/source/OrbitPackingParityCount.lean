import OptimalCylinderPacking
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
The finite parity-vector bijection and binomial law for the shortcut map
already used in this project.  The congruence and powerset proofs below
adapt M. Sharpe's `Collatz/Parity.lean` at commit
ec8174b567d5cab4960024782210b5f5db02bd3a of
https://github.com/msharpe248/collatz .  That source was inspected and its
bytes matched against the pinned commit; this adapted module is checked
separately against this project's definitions and Lean version.

MIT License

Copyright (c) 2026 M. Sharpe

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

set_option autoImplicit false

namespace CollatzOrbitPackingParityCount

open CollatzCylinderPacking

private theorem iterate_succ_start (k n : ℕ) :
    iterate (k + 1) n = iterate k (step n) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterate] using congrArg step ih

private theorem modEq_of_two_mul {a b m : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 * m]) : a ≡ b [MOD m] := by
  have h1 : 2 * a % (2 * m) = 2 * b % (2 * m) := h
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h1
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1

theorem parity_of_modEq (k : ℕ) : ∀ n m, n ≡ m [MOD 2 ^ k] →
    ∀ t, t < k → iterate t n % 2 = iterate t m % 2 := by
  induction k with
  | zero => intro n m _ t ht; omega
  | succ k ih =>
    intro n m h t ht
    have hpar : n % 2 = m % 2 := by
      have hdvd : (2 : ℕ) ∣ 2 ^ (k + 1) := ⟨2 ^ k, by ring⟩
      exact Nat.ModEq.of_dvd hdvd h
    rcases t with _ | t
    · exact hpar
    · have hstep : step n ≡ step m [MOD 2 ^ k] := by
        have hsplit : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rcases Nat.mod_two_eq_zero_or_one n with hp | hp
        · have hmp : m % 2 = 0 := by omega
          apply modEq_of_two_mul
          rw [step_even hp, step_even hmp, ← hsplit]
          exact h
        · have hmp : m % 2 = 1 := by omega
          apply modEq_of_two_mul
          rw [step_odd hp, step_odd hmp, ← hsplit]
          exact (h.mul_left 3).add_right 1
      simpa only [iterate_succ_start] using ih (step n) (step m) hstep t (by omega)

theorem modEq_of_parity (k : ℕ) : ∀ n m,
    (∀ t, t < k → iterate t n % 2 = iterate t m % 2) →
    n ≡ m [MOD 2 ^ k] := by
  induction k with
  | zero => intro n m _; simpa using (Nat.modEq_one : n ≡ m [MOD 1])
  | succ k ih =>
    intro n m hv
    have hpar : n % 2 = m % 2 := hv 0 (by omega)
    have hrec : step n ≡ step m [MOD 2 ^ k] := by
      apply ih
      intro t ht
      simpa only [iterate_succ_start] using hv (t + 1) (by omega)
    have hdouble : 2 * step n ≡ 2 * step m [MOD 2 ^ (k + 1)] := by
      have h2 := Nat.ModEq.mul_left' (c := 2) hrec
      have hsplit : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      rwa [hsplit] at h2
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · have hmp : m % 2 = 0 := by omega
      rwa [step_even hp, step_even hmp] at hdouble
    · have hmp : m % 2 = 1 := by omega
      rw [step_odd hp, step_odd hmp] at hdouble
      have h3 : 3 * n ≡ 3 * m [MOD 2 ^ (k + 1)] :=
        Nat.ModEq.add_right_cancel' 1 hdouble
      have hco : Nat.Coprime (2 ^ (k + 1)) 3 :=
        Nat.Coprime.pow_left (k + 1) (by decide)
      exact Nat.ModEq.cancel_left_of_coprime hco h3

theorem oddCount_eq_sum (k n : ℕ) :
    oddCount k n = ∑ t ∈ Finset.range k, iterate t n % 2 := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih => simp only [oddCount, Finset.sum_range_succ, ih]

theorem oddCount_modEq (k : ℕ) {n m : ℕ} (h : n ≡ m [MOD 2 ^ k]) :
    oddCount k n = oddCount k m := by
  rw [oddCount_eq_sum, oddCount_eq_sum]
  exact Finset.sum_congr rfl
    (fun t ht => parity_of_modEq k n m h t (Finset.mem_range.mp ht))

def oddPositions (k n : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun t => iterate t n % 2 = 1

theorem oddCount_eq_card (k n : ℕ) : oddCount k n = (oddPositions k n).card := by
  unfold oddPositions
  rw [oddCount_eq_sum, Finset.card_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one (iterate t n) with h | h <;> simp [h]

theorem oddPositions_injective (k : ℕ) {r s : ℕ}
    (hr : r < 2 ^ k) (hs : s < 2 ^ k)
    (h : oddPositions k r = oddPositions k s) : r = s := by
  have hp : ∀ t, t < k → iterate t r % 2 = iterate t s % 2 := by
    intro t ht
    have hm : (t ∈ oddPositions k r) ↔ (t ∈ oddPositions k s) := by rw [h]
    simp only [oddPositions, Finset.mem_filter, Finset.mem_range] at hm
    rcases Nat.mod_two_eq_zero_or_one (iterate t r) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (iterate t s) with h2 | h2 <;> omega
  have hmod : r % 2 ^ k = s % 2 ^ k := modEq_of_parity k r s hp
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hmod

theorem parity_pattern_realized (k : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range k) : ∃ r < 2 ^ k, oddPositions k r = S := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le
    (s := Finset.range (2 ^ k)) (t := (Finset.range k).powerset)
    (f := fun r _ => oddPositions k r)
    (hf := fun r _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (hinj := fun r s hr hs h =>
      oddPositions_injective k (Finset.mem_range.mp hr) (Finset.mem_range.mp hs) h)
    (hst := by rw [Finset.card_powerset, Finset.card_range, Finset.card_range])
  obtain ⟨r, hr, hpr⟩ := hsurj S (Finset.mem_powerset.mpr hS)
  exact ⟨r, Finset.mem_range.mp hr, hpr.symm⟩

/-- Exactly `choose k j` starts in the full dyadic range have `j` odd steps. -/
theorem card_oddCount (k j : ℕ) :
    ((Finset.range (2 ^ k)).filter (fun n => oddCount k n = j)).card = k.choose j := by
  have hcard : ((Finset.range k).powersetCard j).card = k.choose j := by
    rw [Finset.card_powersetCard, Finset.card_range]
  rw [← hcard]
  apply Finset.card_bij (fun r _ => oddPositions k r)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [← oddCount_eq_card]
    exact hr.2
  · intro r hr s hs h
    simp only [Finset.mem_filter, Finset.mem_range] at hr hs
    exact oddPositions_injective k hr.1 hs.1 h
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨r, hr, hpr⟩ := parity_pattern_realized k S hS.1
    refine ⟨r, ?_, hpr⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hr, ?_⟩
    rw [oddCount_eq_card, hpr]
    exact hS.2

/-- An arbitrary predicate on the odd count is counted by the corresponding
finite binomial sum. -/
theorem card_oddCount_filter (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (2 ^ k)).filter (fun n => P (oddCount k n))).card =
      ∑ j ∈ (Finset.range (k + 1)).filter P, k.choose j := by
  have hm : Set.MapsTo (oddCount k)
      ((Finset.range (2 ^ k)).filter (fun n => P (oddCount k n)))
      ((Finset.range (k + 1)).filter P) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨Nat.lt_succ_of_le (oddCount_le k n), hn.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjP := (Finset.mem_filter.mp hj).2
  rw [Finset.filter_filter]
  have he : (Finset.range (2 ^ k)).filter (fun n => P (oddCount k n) ∧ oddCount k n = j) =
      (Finset.range (2 ^ k)).filter (fun n => oddCount k n = j) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hjP, h⟩
  rw [he, card_oddCount]

/-- Two complete dyadic periods contain twice the binomial count. -/
theorem card_oddCount_filter_double (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (2 * 2 ^ k)).filter (fun n => P (oddCount k n))).card =
      2 * ∑ j ∈ (Finset.range (k + 1)).filter P, k.choose j := by
  have hshift : (∑ n ∈ Finset.range (2 ^ k),
      if P (oddCount k (2 ^ k + n)) then 1 else 0) =
      ∑ n ∈ Finset.range (2 ^ k), if P (oddCount k n) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro n _
    have hm : 2 ^ k + n ≡ n [MOD 2 ^ k] := by
      exact Nat.add_mod_left (2 ^ k) n
    rw [oddCount_modEq k hm]
  rw [show 2 * 2 ^ k = 2 ^ k + 2 ^ k by omega, Finset.card_filter,
    Finset.sum_range_add, hshift, ← Finset.card_filter, card_oddCount_filter]
  omega

/-- Any collection of starts below two dyadic periods inherits the same
factor-two bound.  No orbit or independence assumption is needed. -/
theorem card_subset_double_range_le {k : ℕ} {S : Finset ℕ}
    (P : ℕ → Prop) [DecidablePred P]
    (hS : S ⊆ Finset.range (2 * 2 ^ k))
    (hP : ∀ n ∈ S, P (oddCount k n)) :
    S.card ≤ 2 * ∑ j ∈ (Finset.range (k + 1)).filter P, k.choose j := by
  calc
    S.card ≤ ((Finset.range (2 * 2 ^ k)).filter (fun n => P (oddCount k n))).card := by
      apply Finset.card_le_card
      intro n hn
      exact Finset.mem_filter.mpr ⟨hS hn, hP n hn⟩
    _ = 2 * ∑ j ∈ (Finset.range (k + 1)).filter P, k.choose j :=
      card_oddCount_filter_double k P

#print axioms parity_of_modEq
#print axioms modEq_of_parity
#print axioms card_oddCount
#print axioms card_oddCount_filter
#print axioms card_subset_double_range_le

end CollatzOrbitPackingParityCount
