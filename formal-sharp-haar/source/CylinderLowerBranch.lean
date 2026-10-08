import AdmissibleCylinderWords

set_option autoImplicit false

namespace CollatzCylinderPacking.LowerBranch

theorem iterate_succ_first (A n : ℕ) :
    iterate (A + 1) n = iterate A (step n) := by
  induction A with
  | zero => rfl
  | succ A ih => exact congrArg step ih

theorem oddCount_succ_first (A n : ℕ) :
    oddCount (A + 1) n = n % 2 + oddCount A (step n) := by
  induction A with
  | zero => simp [oddCount, iterate]
  | succ A ih =>
    change oddCount (A + 1) n + iterate (A + 1) n % 2 =
      n % 2 + (oddCount A (step n) + iterate A (step n) % 2)
    rw [ih, iterate_succ_first]
    omega

theorem reverseItinerary_succ_first (A n : ℕ) :
    reverseItinerary (A + 1) n = reverseItinerary A (step n) ++ [n % 2] := by
  induction A with
  | zero => simp [reverseItinerary, iterate]
  | succ A ih =>
    change iterate (A + 1) n % 2 :: reverseItinerary (A + 1) n =
      (iterate A (step n) % 2 :: reverseItinerary A (step n)) ++ [n % 2]
    rw [iterate_succ_first, ih]
    rfl

theorem step_two_mul_sub_one {m : ℕ} (hm : 0 < m) :
    step (2 * m - 1) = 3 * m - 1 := by
  have ho : (2 * m - 1) % 2 = 1 := by omega
  have hs := step_odd ho
  omega

/-- The complete actual itinerary of the all-odd finite branch. -/
theorem all_odd_run (A b : ℕ) (hb : 0 < b) :
    iterate A (2 ^ A * b - 1) = 3 ^ A * b - 1 ∧
    oddCount A (2 ^ A * b - 1) = A ∧
    reverseItinerary A (2 ^ A * b - 1) = List.replicate A 1 := by
  induction A generalizing b with
  | zero => simp [iterate, oddCount, reverseItinerary]
  | succ A ih =>
    have hm : 0 < 2 ^ A * b := by positivity
    have hstart : 2 ^ (A + 1) * b - 1 = 2 * (2 ^ A * b) - 1 := by
      rw [pow_succ]
      congr 1
      ring
    have ho : (2 ^ (A + 1) * b - 1) % 2 = 1 := by
      rw [hstart]
      omega
    have hs : step (2 ^ (A + 1) * b - 1) = 2 ^ A * (3 * b) - 1 := by
      rw [hstart, step_two_mul_sub_one hm]
      congr 1
      ring
    have hi := ih (3 * b) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [iterate_succ_first, hs, hi.1]
      rw [pow_succ]
      congr 1
      ring
    · rw [oddCount_succ_first, ho, hs, hi.2.1]
      omega
    · rw [reverseItinerary_succ_first, hs, hi.2.2, ho]
      simp [List.replicate_add]

theorem encode_ones (k : ℕ) : encode (List.replicate k 1) = List.replicate k 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, encode, ih]

/-- A positive representative of the repeated a=1 branch at the cylinder -1.
The target 3^k-1 is even; the source 2^k-1 is odd for k>=1. -/
theorem all_one_branch_admissible {k : ℕ} (hk : 0 < k) :
    Admissible (3 ^ k - 1) (List.replicate k 1) (2 ^ k - 1) := by
  have hi := all_odd_run k 1 (by decide)
  simp only [mul_one] at hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_replicate] at ha
    omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ j := by positivity
    omega
  · simpa using hi.1
  · simpa only [List.sum_replicate, nsmul_eq_mul, mul_one, encode_ones] using hi.2.2

#print axioms all_odd_run
#print axioms all_one_branch_admissible

end CollatzCylinderPacking.LowerBranch
