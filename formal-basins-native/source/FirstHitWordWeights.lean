import FinitePathInverseWords
import OrbitCorrectionProduct

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- Prefix correction product, excluding the terminal state. -/
noncomputable def pathCorrection (A q : ℕ) : ℝ :=
  ∏ i ∈ Finset.range A, (1 + CollatzCanonical.Correction.oddCorrection (iterate i q))

/-- Reciprocal prefix correction. -/
noncomputable def pathWeight (A q : ℕ) : ℝ := (pathCorrection A q)⁻¹

theorem one_le_pathCorrection (A q : ℕ) : 1 ≤ pathCorrection A q :=
  (CollatzCanonical.Correction.finite_orbit_product_bounds q A).1

theorem pathWeight_bounds (A q : ℕ) : 0 < pathWeight A q ∧ pathWeight A q ≤ 1 := by
  have hp : 0 < pathCorrection A q := lt_of_lt_of_le (by norm_num) (one_le_pathCorrection A q)
  constructor
  · exact inv_pos.mpr hp
  · exact inv_le_one_of_one_le₀ (one_le_pathCorrection A q)

/-- Exact inverse-word weight of an actual finite hitting path. -/
theorem hitting_path_weight {A q N : ℕ} (hq : 0 < q) (hhit : iterate A q = N) :
    (3 : ℝ) ^ oddCount A q * (1 / 2 : ℝ) ^ A = (N : ℝ) * pathWeight A q / q := by
  have hid := CollatzCanonical.Correction.iterate_correction_identity A hq
  rw [hhit] at hid
  have hp : pathCorrection A q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (one_le_pathCorrection A q))
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  change (2 : ℝ) ^ A * (N : ℝ) = (3 : ℝ) ^ oddCount A q * q * pathCorrection A q at hid
  rw [one_div_pow]
  unfold pathWeight
  field_simp
  nlinarith only [hid]

/-- The paper's total first-hit weight: reciprocal prefix correction on the
basin of N and zero outside that basin. -/
noncomputable def firstHitWeight (N q : ℕ) : ℝ := by
  classical
  exact if h : ∃ A, iterate A q = N then pathWeight (Nat.find h) q else 0

theorem firstHit_find {q N : ℕ} (hhit : ∃ A, iterate A q = N) :
    FirstHit q N (Nat.find hhit) := by
  refine ⟨Nat.find_spec hhit, ?_⟩
  intro i hi
  exact Nat.find_min hhit hi

theorem firstHit_time_unique {q N A B : ℕ}
    (hA : FirstHit q N A) (hB : FirstHit q N B) : A = B := by
  rcases lt_trichotomy A B with h | h | h
  · exact False.elim (hB.2 A h hA.1)
  · exact h
  · exact False.elim (hA.2 B h hB.1)

theorem firstHitWeight_eq_pathWeight {q N A : ℕ} (hfirst : FirstHit q N A) :
    firstHitWeight N q = pathWeight A q := by
  classical
  have hh : ∃ A, iterate A q = N := ⟨A, hfirst.1⟩
  have he := firstHit_time_unique (firstHit_find hh) hfirst
  simp only [firstHitWeight, dif_pos hh, he]

theorem firstHitWeight_bounds (N q : ℕ) : 0 ≤ firstHitWeight N q ∧ firstHitWeight N q ≤ 1 := by
  classical
  unfold firstHitWeight
  split_ifs
  · exact ⟨(pathWeight_bounds _ _).1.le, (pathWeight_bounds _ _).2⟩
  · norm_num

/-- The exact first-hit weight identity, with w_N defined on all integers. -/
theorem first_hit_weight {A q N : ℕ} (hq : 0 < q) (hfirst : FirstHit q N A) :
    (3 : ℝ) ^ oddCount A q * (1 / 2 : ℝ) ^ A = (N : ℝ) * firstHitWeight N q / q := by
  rw [firstHitWeight_eq_pathWeight hfirst]
  exact hitting_path_weight hq hfirst.1

/-- An actual odd first-hit path has a ValidWord representation whose
arithmetic inverse weight is exactly N w_N(q) / q. -/
theorem first_hit_word_weight {A q N : ℕ} (hq : 0 < q) (hodd : q % 2 = 1)
    (hfirst : FirstHit q N A) :
    ∃ w : GeometricWord (oddCount A q), ValidWord (oddCount A q) N w ∧
      wordLength (oddCount A q) w = A ∧ tupleEndpoint N (wordList (oddCount A q) w) = q ∧
      (3 : ℝ) ^ oddCount A q * arithmeticTerm (oddCount A q) N w =
        (N : ℝ) * firstHitWeight N q / q := by
  classical
  obtain ⟨w, hv, hl, he⟩ := first_hit_word hq hodd hfirst
  refine ⟨w, hv, hl, he, ?_⟩
  simp only [arithmeticTerm, if_pos hv, hl]
  exact first_hit_weight hq hfirst

end CollatzCylinderPacking.Arithmetic
