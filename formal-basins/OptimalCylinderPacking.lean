import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace CollatzCylinderPacking

def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def iterate : ℕ → ℕ → ℕ
  | 0, n => n
  | A + 1, n => step (iterate A n)

def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | A + 1, n => oddCount A n + iterate A n % 2

theorem oddCount_le (A n : ℕ) : oddCount A n ≤ A := by
  induction A with
  | zero => simp [oddCount]
  | succ A ih =>
    have hm := Nat.mod_lt (iterate A n) (by decide : 0 < 2)
    simp only [oddCount]
    omega

theorem step_even {n : ℕ} (h : n % 2 = 0) : 2 * step n = n := by
  simp only [step, h, if_pos]
  omega

theorem step_odd {n : ℕ} (h : n % 2 = 1) : 2 * step n = 3 * n + 1 := by
  simp only [step, h, Nat.one_ne_zero, if_false]
  omega

/-- Integer form of the affine slope and offset bounds. The second inequality
is equivalent to offset ≤ (3/2)^k - 1, where k is the odd count. -/
theorem scaled_bounds (A n : ℕ) :
    3 ^ oddCount A n * n ≤ 2 ^ A * iterate A n ∧
    2 ^ A * iterate A n + 2 ^ A ≤
      3 ^ oddCount A n * n + 3 ^ oddCount A n * 2 ^ (A - oddCount A n) := by
  induction A with
  | zero => simp [iterate, oddCount]
  | succ A ih =>
    have hk := oddCount_le A n
    have hm := Nat.mod_lt (iterate A n) (by decide : 0 < 2)
    rcases ih with ⟨hlo, hup⟩
    by_cases he : iterate A n % 2 = 0
    · have hs := step_even he
      have hsm := congrArg (fun x : ℕ => 2 ^ A * x) hs
      have hexp : A + 1 - oddCount A n = (A - oddCount A n) + 1 := by omega
      have hpow : 2 ^ A = 2 ^ oddCount A n * 2 ^ (A - oddCount A n) := by
        rw [← pow_add]
        congr 1
        omega
      have hsmall : 2 ^ A ≤ 3 ^ oddCount A n * 2 ^ (A - oddCount A n) := by
        rw [hpow]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
      simp only [iterate, oddCount, he, Nat.add_zero, hexp, pow_succ]
      constructor <;> nlinarith
    · have ho : iterate A n % 2 = 1 := by omega
      have hs := step_odd ho
      have hsm := congrArg (fun x : ℕ => 2 ^ A * x) hs
      dsimp only at hsm
      have hlo3 := Nat.mul_le_mul_left 3 hlo
      simp only [iterate, oddCount, ho, Nat.add_sub_add_right, pow_succ]
      constructor
      · nlinarith only [hlo3, hsm, Nat.zero_le (2 ^ A)]
      · nlinarith

/-- Two starts with the same length, odd count, and endpoint lie in an
interval shorter than 2^(A-k), uniformly in that endpoint. -/
theorem endpoint_span {A k N x y : ℕ}
    (hx : iterate A x = N) (hy : iterate A y = N)
    (hkx : oddCount A x = k) (hky : oddCount A y = k) :
    y < x + 2 ^ (A - k) := by
  obtain ⟨_, hu⟩ := scaled_bounds A x
  obtain ⟨hl, _⟩ := scaled_bounds A y
  rw [hx, hkx] at hu
  rw [hy, hky] at hl
  have hpos : 0 < (2 : ℕ) ^ A := by positivity
  by_contra hn
  have hmul := Nat.mul_le_mul_left (3 ^ k) (Nat.le_of_not_gt hn)
  nlinarith

theorem odd_card_le_of_span {S : Finset ℕ} {W : ℕ}
    (hodd : ∀ n ∈ S, n % 2 = 1)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, y < x + W) :
    S.card ≤ W / 2 + 1 := by
  classical
  by_cases hempty : S = ∅
  · simp [hempty]
  have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let lo := S.min' hne
  have hlo : lo ∈ S := Finset.min'_mem S hne
  have hlow : ∀ n ∈ S, lo ≤ n := fun n hn => Finset.min'_le S n hn
  have hmap : Set.MapsTo (fun n => n / 2 - lo / 2) S
      (Finset.range (W / 2 + 1)) := by
    intro n hn
    have hs := hspan lo hlo n hn
    have hl := hlow n hn
    have ho := hodd n hn
    have hol := hodd lo hlo
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun n => n / 2 - lo / 2) S := by
    intro x hx y hy heq
    change x / 2 - lo / 2 = y / 2 - lo / 2 at heq
    have hxl := hlow x hx
    have hyl := hlow y hy
    have hxo := hodd x hx
    have hyo := hodd y hy
    omega
  calc
    S.card ≤ (Finset.range (W / 2 + 1)).card :=
      Finset.card_le_card_of_injOn (fun n => n / 2 - lo / 2) hmap hinj
    _ = W / 2 + 1 := Finset.card_range _

/-- Uniform endpoint-packing bound used by the stationary-cylinder argument.
All hypotheses describe actual finite shortcut trajectories. -/
theorem odd_endpoint_card_bound {A k N : ℕ} {S : Finset ℕ}
    (hodd : ∀ n ∈ S, n % 2 = 1)
    (hend : ∀ n ∈ S, iterate A n = N)
    (hcount : ∀ n ∈ S, oddCount A n = k) :
    S.card ≤ 2 ^ (A - k) / 2 + 1 := by
  apply odd_card_le_of_span hodd
  intro x hx y hy
  exact endpoint_span (hend x hx) (hend y hy) (hcount x hx) (hcount y hy)

def endpointSet (A k N : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ A * N + 1)).filter
    (fun n => n % 2 = 1 ∧ iterate A n = N ∧ oddCount A n = k)

theorem mem_endpointSet {A k N n : ℕ} : n ∈ endpointSet A k N ↔
    n % 2 = 1 ∧ iterate A n = N ∧ oddCount A n = k := by
  simp only [endpointSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hl := (scaled_bounds A n).1
    rw [h.2.1, h.2.2] at hl
    have hpow : 1 ≤ (3 : ℕ) ^ k := by
      have hp : 0 < (3 : ℕ) ^ k := by positivity
      omega
    have hn : n ≤ 3 ^ k * n := by simpa using Nat.mul_le_mul_right n hpow
    exact ⟨by omega, h⟩

def endpointCount (A k N : ℕ) : ℕ := (endpointSet A k N).card

theorem endpointCount_bound (A k N : ℕ) :
    endpointCount A k N ≤ 2 ^ (A - k) / 2 + 1 := by
  apply odd_endpoint_card_bound
  · intro n hn
    exact (mem_endpointSet.mp hn).1
  · intro n hn
    exact (mem_endpointSet.mp hn).2.1
  · intro n hn
    exact (mem_endpointSet.mp hn).2.2

/-- Denominator-free form of c_(A,k)(N) ≤ 2^(A-k-1)+1. -/
theorem endpointCount_scaled_bound (A k N : ℕ) :
    2 * endpointCount A k N ≤ 2 ^ (A - k) + 2 := by
  have h := endpointCount_bound A k N
  omega

#print axioms scaled_bounds
#print axioms endpoint_span
#print axioms odd_endpoint_card_bound
#print axioms endpointCount_scaled_bound

end CollatzCylinderPacking
