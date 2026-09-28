import FirstHitWeightTransport

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem firstHitWeight_self (N : ℕ) : firstHitWeight N N = 1 := by
  have hf : FirstHit N N 0 := ⟨rfl, by intro i hi; omega⟩
  rw [firstHitWeight_eq_pathWeight hf]
  simp [pathWeight, pathCorrection]

/-- An initial even shortcut step contributes no correction unless its
starting point is already the target. -/
theorem firstHitWeight_halving {N q : ℕ} (hne : 2 * q ≠ N) :
    firstHitWeight N (2 * q) = firstHitWeight N q := by
  have h := firstHitWeight_prefix_factorization (A := 1) (q := 2 * q) (N := N) (by
    intro i hi
    have hi0 : i = 0 := by omega
    simpa only [hi0, iterate] using hne)
  simpa [pathWeight, pathCorrection, CollatzCanonical.Correction.oddCorrection,
    iterate, step_two_mul] using h

theorem firstHitWeight_halving_defect (N q : ℕ) :
    0 ≤ firstHitWeight N (2 * q) - firstHitWeight N q ∧
      firstHitWeight N (2 * q) - firstHitWeight N q ≤ 1 := by
  by_cases h : 2 * q = N
  · rw [h, firstHitWeight_self]
    have hw := firstHitWeight_bounds N q
    constructor <;> linarith
  · rw [firstHitWeight_halving h]
    norm_num

theorem firstHitWeight_halving_defect_supported (N q : ℕ) :
    firstHitWeight N (2 * q) - firstHitWeight N q =
      if 2 * q = N then 1 - firstHitWeight N q else 0 := by
  by_cases h : 2 * q = N
  · simp [h, firstHitWeight_self]
  · simp only [if_neg h, firstHitWeight_halving h, sub_self]

end CollatzCylinderPacking.Arithmetic
