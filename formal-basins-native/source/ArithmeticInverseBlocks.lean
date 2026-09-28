import CylinderLowerBranch

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

open LowerBranch

def inverseValue (a v : ℕ) : ℕ := (2 ^ a * v - 1) / 3

def ValidBlock (a v : ℕ) : Prop := 0 < a ∧ 3 ∣ 2 ^ a * v - 1

theorem step_two_mul (m : ℕ) : step (2 * m) = m := by
  have he : (2 * m) % 2 = 0 := by omega
  have hs := step_even he
  omega

theorem even_run (r v : ℕ) :
    iterate r (2 ^ r * v) = v ∧
    oddCount r (2 ^ r * v) = 0 ∧
    reverseItinerary r (2 ^ r * v) = List.replicate r 0 := by
  induction r with
  | zero => simp [iterate, oddCount, reverseItinerary]
  | succ r ih =>
    have heq : 2 ^ (r + 1) * v = 2 * (2 ^ r * v) := by rw [pow_succ]; ring
    have he : (2 ^ (r + 1) * v) % 2 = 0 := by rw [heq]; omega
    have hs : step (2 ^ (r + 1) * v) = 2 ^ r * v := by rw [heq, step_two_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [iterate_succ_first, hs, ih.1]
    · rw [oddCount_succ_first, he, hs, ih.2.1]
    · rw [reverseItinerary_succ_first, he, hs, ih.2.2]
      simp [List.replicate_add]

/-- A single inverse arithmetic block has exactly the required actual parity
word, including when its final target v is even. -/
theorem block_path {a v m : ℕ} (ha : 0 < a) (h : 3 * m + 1 = 2 ^ a * v) :
    m % 2 = 1 ∧ iterate a m = v ∧ oddCount a m = 1 ∧
    reverseItinerary a m = List.replicate (a - 1) 0 ++ [1] := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have hh : 3 * m + 1 = 2 * (2 ^ r * v) := by
    rw [h, pow_succ]
    ring
  have ho : m % 2 = 1 := by omega
  have hstep := step_odd ho
  have hs : step m = 2 ^ r * v := by omega
  have he := even_run r v
  refine ⟨ho, ?_, ?_, ?_⟩
  · rw [iterate_succ_first, hs, he.1]
  · rw [oddCount_succ_first, ho, hs, he.2.1]
  · rw [reverseItinerary_succ_first, ho, hs, he.2.2]
    simp

theorem inverse_identity {a v : ℕ} (hv : 0 < v) (h : ValidBlock a v) :
    3 * inverseValue a v + 1 = 2 ^ a * v := by
  have hp : 0 < 2 ^ a * v := by positivity
  have hd := Nat.mul_div_cancel' h.2
  unfold inverseValue
  omega

theorem inverse_positive {a v : ℕ} (hv : 0 < v) (h : ValidBlock a v) :
    0 < inverseValue a v := by
  have hi := inverse_identity hv h
  have ha : 2 ≤ (2 : ℕ) ^ a := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) h.1
    simpa using hp
  have hm : 2 ^ a ≤ 2 ^ a * v := by
    have ht := Nat.mul_le_mul_left (2 ^ a) (Nat.succ_le_iff.mpr hv)
    simpa using ht
  omega

theorem inverse_odd {a v : ℕ} (hv : 0 < v) (h : ValidBlock a v) :
    inverseValue a v % 2 = 1 :=
  (block_path h.1 (inverse_identity hv h)).1

theorem inverse_block_admissible {a v : ℕ} (hv : 0 < v) (h : ValidBlock a v) :
    Admissible v [a] (inverseValue a v) := by
  have ht := block_path h.1 (inverse_identity hv h)
  refine ⟨?_, ht.1, ?_, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    simpa only [hb] using h.1
  · simpa using ht.2.1
  · simpa [encode] using ht.2.2.2

#print axioms block_path
#print axioms inverse_positive
#print axioms inverse_block_admissible

end CollatzCylinderPacking.Arithmetic
