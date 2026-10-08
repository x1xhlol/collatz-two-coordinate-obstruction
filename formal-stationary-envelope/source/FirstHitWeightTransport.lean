import FirstHitWordWeights
import UniformOrbitCorrection

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

theorem pathCorrection_add (A B q : ℕ) :
    pathCorrection (A + B) q = pathCorrection A q * pathCorrection B (iterate A q) := by
  unfold pathCorrection
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [iterate_add]

theorem pathWeight_add (A B q : ℕ) :
    pathWeight (A + B) q = pathWeight A q * pathWeight B (iterate A q) := by
  rw [pathWeight, pathCorrection_add, mul_inv]
  rfl

theorem hit_iff_suffix_of_prefix_avoids {A q N : ℕ}
    (havoid : ∀ i < A, iterate i q ≠ N) :
    (∃ B, iterate B q = N) ↔ ∃ B, iterate B (iterate A q) = N := by
  constructor
  · rintro ⟨B, hB⟩
    have hAB : A ≤ B := by
      by_contra h
      exact havoid B (Nat.lt_of_not_ge h) hB
    refine ⟨B - A, ?_⟩
    rw [← iterate_add, Nat.add_sub_of_le hAB, hB]
  · rintro ⟨B, hB⟩
    exact ⟨A + B, by rw [iterate_add, hB]⟩

theorem firstHit_prepend {A B q N : ℕ}
    (havoid : ∀ i < A, iterate i q ≠ N) (hsuffix : FirstHit (iterate A q) N B) :
    FirstHit q N (A + B) := by
  refine ⟨by rw [iterate_add, hsuffix.1], ?_⟩
  intro i hi
  by_cases hiA : i < A
  · exact havoid i hiA
  · have hAi : A ≤ i := Nat.le_of_not_gt hiA
    have he : iterate i q = iterate (i - A) (iterate A q) := by
      rw [← iterate_add, Nat.add_sub_of_le hAi]
    rw [he]
    exact hsuffix.2 (i - A) (by omega)

/-- First-hit weights factor along a target-avoiding prefix, including starts
outside the basin of the target. -/
theorem firstHitWeight_prefix_factorization {A q N : ℕ}
    (havoid : ∀ i < A, iterate i q ≠ N) :
    firstHitWeight N q = pathWeight A q * firstHitWeight N (iterate A q) := by
  classical
  by_cases hh : ∃ B, iterate B (iterate A q) = N
  · have hsuffix := firstHit_find hh
    rw [firstHitWeight_eq_pathWeight (firstHit_prepend havoid hsuffix),
      firstHitWeight_eq_pathWeight hsuffix, pathWeight_add]
  · have hq : ¬∃ B, iterate B q = N :=
      fun h => hh ((hit_iff_suffix_of_prefix_avoids havoid).mp h)
    simp only [firstHitWeight, dif_neg hq, dif_neg hh, mul_zero]

theorem firstHitWeight_prefix_difference {A q N : ℕ}
    (havoid : ∀ i < A, iterate i q ≠ N) :
    |firstHitWeight N q - firstHitWeight N (iterate A q)| ≤ 1 - pathWeight A q := by
  have hp := pathWeight_bounds A q
  have hw := firstHitWeight_bounds N (iterate A q)
  rw [firstHitWeight_prefix_factorization havoid]
  have hm : pathWeight A q * firstHitWeight N (iterate A q) ≤
      firstHitWeight N (iterate A q) := by nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hm)]
  nlinarith

theorem reciprocal_product_error_of_exp_bound {P a : ℝ} (hP : 1 ≤ P)
    (ha : P ≤ Real.exp a) : 1 - P⁻¹ ≤ a := by
  have hP0 : 0 < P := by linarith
  have hi : (Real.exp a)⁻¹ ≤ P⁻¹ := inv_anti₀ hP0 ha
  rw [← Real.exp_neg] at hi
  have he := Real.add_one_le_exp (-a)
  linarith

/-- A uniform packing bound makes the actual first-hit weight nearly invariant
across every distinct prefix whose odd source states lie above a barrier. -/
theorem firstHitWeight_uniform_prefix_transport (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A q N : ℕ), 0 < q →
      (∀ i < A, iterate i q ≠ N) →
      Set.InjOn (fun i => iterate i q) (Finset.range A) →
      ∀ M : ℝ, 1 ≤ M →
        (∀ i < A, iterate i q % 2 = 1 → M ≤ (iterate i q : ℝ)) →
        |firstHitWeight N q - firstHitWeight N (iterate A q)| ≤ C * M ^ (b - 1) := by
  obtain ⟨R, hR, hbound⟩ :=
    CollatzCanonical.UniformCorrection.uniform_finite_path_correction_bounds b hbβ hb1
  refine ⟨R / 3, by positivity, ?_⟩
  intro A q N hq havoid hinj M hM hhigh
  have hp := hbound A (fun i => iterate i q) hq (fun _ _ => rfl) hinj
  have he : pathCorrection A q ≤ Real.exp ((R / 3) * M ^ (b - 1)) := hp.2.2 M hM hhigh
  have hw := reciprocal_product_error_of_exp_bound (one_le_pathCorrection A q) he
  exact (firstHitWeight_prefix_difference havoid).trans hw

#print axioms pathCorrection_add
#print axioms firstHitWeight_prefix_factorization
#print axioms firstHitWeight_uniform_prefix_transport

end CollatzCylinderPacking.Arithmetic
