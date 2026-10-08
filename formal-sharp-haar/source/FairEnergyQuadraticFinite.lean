import FairEnergyFinite
import FairEnergyMoments
import QuotientFiberBounds

set_option autoImplicit false
open scoped BigOperators

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

theorem fixed_total_fiber_card_sq_le_twice {k A : ℕ} (v : ZMod (3 ^ k))
    (s : Finset (GeometricWord k))
    (hA : ∀ w ∈ s, wordLength k w = A)
    (hv : ∀ w ∈ s, wordResidue k w = v) :
    (s.card : ℝ) ^ 2 ≤ 2 * ∑ w ∈ s, (1 + wordTranslation k w) := by
  apply card_sq_le_twice_quotient_weight s
    (fun w => affineNumerator (wordList k w) / 3 ^ k) (wordTranslation k)
  · intro w hw u hu he
    exact numerator_quotient_injective_on_fiber v
      ⟨hA w hw, hv w hw⟩ ⟨hA u hu, hv u hu⟩ he
  · intro w _
    exact numerator_quotient_le_translation k w

theorem fixed_total_scaled_sq_le_quadratic {k A : ℕ}
    (v : ZMod (3 ^ k)) (s : Finset (GeometricWord k))
    (hA : ∀ w ∈ s, wordLength k w = A)
    (hv : ∀ w ∈ s, wordResidue k w = v) :
    (3 : ℝ) ^ k * (A : ℝ) ^ 2 *
        ((1 / 2 : ℝ) ^ A * (s.card : ℝ)) ^ 2 ≤
      2 * ∑ w ∈ s, quadraticMomentTerm k w := by
  have hcard := fixed_total_fiber_card_sq_le_twice v s hA hv
  calc
    _ = ((3 : ℝ) ^ k * (1 / 4 : ℝ) ^ A * (A : ℝ) ^ 2) * (s.card : ℝ) ^ 2 := by
      rw [mul_pow, half_pow_sq]
      ring
    _ ≤ ((3 : ℝ) ^ k * (1 / 4 : ℝ) ^ A * (A : ℝ) ^ 2) *
        (2 * ∑ w ∈ s, (1 + wordTranslation k w)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 2 * ∑ w ∈ s, quadraticMomentTerm k w := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [quadraticMomentTerm, biasedWordWeight, hA w hw]
      ring

theorem residue_finite_sum_scaled_sq_le_quadratic {k : ℕ} (hk : 1 ≤ k)
    (v : ZMod (3 ^ k)) (s : Finset (GeometricWord k))
    (hv : ∀ w ∈ s, wordResidue k w = v) :
    (3 : ℝ) ^ k * (∑ w ∈ s, (1 / 2 : ℝ) ^ wordLength k w) ^ 2 ≤
      (4 / (k : ℝ)) * ∑ w ∈ s, quadraticMomentTerm k w := by
  classical
  let D := s.image (wordLength k)
  let F := fun A => s.filter (fun w => wordLength k w = A)
  have hD : ∀ w ∈ s, wordLength k w ∈ D := fun w hw => Finset.mem_image_of_mem _ hw
  have hDk : ∀ A ∈ D, k ≤ A := by
    intro A hA
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hA
    exact wordLength_ge_depth k w
  have hmass : (∑ w ∈ s, (1 / 2 : ℝ) ^ wordLength k w) =
      ∑ A ∈ D, (1 / 2 : ℝ) ^ A * ((F A).card : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hD]
    apply Finset.sum_congr rfl
    intro A _
    calc
      (∑ w ∈ s with wordLength k w = A, (1 / 2 : ℝ) ^ wordLength k w) =
          ∑ _w ∈ F A, (1 / 2 : ℝ) ^ A := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [(Finset.mem_filter.mp hw).2]
      _ = _ := by simp [mul_comm]
  have hfiber : ∀ A ∈ D,
      (3 : ℝ) ^ k * (A : ℝ) ^ 2 *
          ((1 / 2 : ℝ) ^ A * ((F A).card : ℝ)) ^ 2 ≤
        2 * ∑ w ∈ F A, quadraticMomentTerm k w := by
    intro A _
    apply fixed_total_scaled_sq_le_quadratic v (F A)
    · intro w hw
      exact (Finset.mem_filter.mp hw).2
    · intro w hw
      exact hv w (Finset.mem_filter.mp hw).1
  rw [hmass]
  calc
    _ ≤ (3 : ℝ) ^ k * ((2 / (k : ℝ)) *
        ∑ A ∈ D, (A : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ A * ((F A).card : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (weighted_sum_sq_le D k (fun A => (1 / 2 : ℝ) ^ A * ((F A).card : ℝ)) hk hDk)
        (by positivity)
    _ = (2 / (k : ℝ)) * ∑ A ∈ D,
        (3 : ℝ) ^ k * (A : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ A * ((F A).card : ℝ)) ^ 2 := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ ≤ (2 / (k : ℝ)) * ∑ A ∈ D, 2 * ∑ w ∈ F A, quadraticMomentTerm k w :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfiber) (by positivity)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hD (quadraticMomentTerm k)]
      ring

theorem finite_residue_energy_le_quadratic_moment (k : ℕ) (hk : 1 ≤ k)
    (s : Finset (GeometricWord k)) :
    (3 : ℝ) ^ k * (∑ v : ZMod (3 ^ k), (∑ w ∈ s, residueTerm k v w) ^ 2) ≤
      (4 / (k : ℝ)) * ∑ w ∈ s, quadraticMomentTerm k w := by
  classical
  have hmass (v : ZMod (3 ^ k)) : (∑ w ∈ s, residueTerm k v w) =
      ∑ w ∈ s with wordResidue k w = v, (1 / 2 : ℝ) ^ wordLength k w := by
    simp only [Finset.sum_filter, residueTerm, eq_comm]
  have hpoint (v : ZMod (3 ^ k)) :
      (3 : ℝ) ^ k * (∑ w ∈ s, residueTerm k v w) ^ 2 ≤
        (4 / (k : ℝ)) * ∑ w ∈ s with wordResidue k w = v, quadraticMomentTerm k w := by
    rw [hmass]
    apply residue_finite_sum_scaled_sq_le_quadratic hk v
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  calc
    _ = ∑ v : ZMod (3 ^ k), (3 : ℝ) ^ k * (∑ w ∈ s, residueTerm k v w) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ v : ZMod (3 ^ k),
        (4 / (k : ℝ)) * ∑ w ∈ s with wordResidue k w = v, quadraticMomentTerm k w :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]

end CollatzCylinderPacking.Arithmetic.FairEnergy
