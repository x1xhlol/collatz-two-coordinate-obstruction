import CollatzForwardRealContraction
import CollatzForwardRealWordGrowth

namespace CollatzResearch.ForwardRealTwoCoordinateNecessary

open Matrix CollatzCertificate

theorem positive_subeigenrow_of_two_coordinate_bounds
    (A : Mat (Fin 2)) (hA : EntrywiseLE 0 A)
    (h00 : A 0 0 < 1) (h11 : A 1 1 < 1)
    (hcross : A 0 1 * A 1 0 < (1 - A 0 0) * (1 - A 1 1)) :
    ∃ w : Vec (Fin 2), ∃ l : ℝ,
      (∀ i, 0 < w i) ∧ 0 ≤ l ∧ l < 1 ∧ w ᵥ* A ≤ l • w := by
  let w : Vec (Fin 2) := ![1 - A 1 1 + A 1 0, 1 - A 0 0 + A 0 1]
  let D := (1 - A 0 0) * (1 - A 1 1) - A 0 1 * A 1 0
  have hD : 0 < D := sub_pos.mpr hcross
  have hw : ∀ i, 0 < w i := by
    intro i
    fin_cases i
    · change 0 < 1 - A 1 1 + A 1 0
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr h11) (hA 1 0)
    · change 0 < 1 - A 0 0 + A 0 1
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr h00) (hA 0 1)
  have hrow (i : Fin 2) : (w ᵥ* A) i = w i - D := by
    fin_cases i <;> simp [w, D, vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  have hnonneg (i : Fin 2) : 0 ≤ (w ᵥ* A) i := by
    simpa only [vecMul, dotProduct, Fin.sum_univ_two] using
      add_nonneg (mul_nonneg (hw 0).le (hA 0 i)) (mul_nonneg (hw 1).le (hA 1 i))
  let S := w 0 + w 1
  have hS : 0 < S := add_pos (hw 0) (hw 1)
  have hDS : D ≤ S := by
    have hi := hnonneg 0
    rw [hrow] at hi
    dsimp only [S]
    linarith [hw 1]
  let t := D / S
  have ht : 0 < t := div_pos hD hS
  have ht1 : t ≤ 1 := (div_le_one hS).mpr hDS
  have htS : t * S = D := div_mul_cancel₀ D (ne_of_gt hS)
  refine ⟨w, 1 - t, hw, sub_nonneg.mpr ht1, by linarith, ?_⟩
  intro i
  have hwi : w i ≤ S := by
    fin_cases i
    · exact le_add_of_nonneg_right (hw 1).le
    · exact le_add_of_nonneg_left (hw 0).le
  have htw : t * w i ≤ D := (mul_le_mul_of_nonneg_left hwi ht.le).trans_eq htS
  rw [hrow]
  change w i - D ≤ (1 - t) * w i
  nlinarith

theorem gaps_zero_of_two_coordinate_bounds
    (d : ForwardRealWordGrowth.Data (Fin 2)) (i : Fin 2)
    (h00 : d.A.matrix 0 0 < 1) (h11 : d.A.matrix 1 1 < 1)
    (hcross : d.A.matrix 0 1 * d.A.matrix 1 0 <
      (1 - d.A.matrix 0 0) * (1 - d.A.matrix 1 1)) :
    d.gap i .e = 0 ∧ d.gap i .f = 0 ∧ d.gap i .g = 0 := by
  obtain ⟨w, l, hw, hl, hl1, hc⟩ := positive_subeigenrow_of_two_coordinate_bounds
    d.A.matrix d.hA.1 h00 h11 hcross
  exact d.gaps_zero_of_positive_subeigenrow i w hw l hl hl1 hc

theorem positive_eligible_gap_requires_noncontraction
    (d : ForwardRealWordGrowth.Data (Fin 2)) (i : Fin 2)
    (hs : 0 < d.gap i .e ∨ 0 < d.gap i .f ∨ 0 < d.gap i .g) :
    1 ≤ d.A.matrix 0 0 ∨ 1 ≤ d.A.matrix 1 1 ∨
      (1 - d.A.matrix 0 0) * (1 - d.A.matrix 1 1) ≤
        d.A.matrix 0 1 * d.A.matrix 1 0 := by
  by_cases h00 : 1 ≤ d.A.matrix 0 0
  · exact Or.inl h00
  by_cases h11 : 1 ≤ d.A.matrix 1 1
  · exact Or.inr (Or.inl h11)
  apply Or.inr ∘ Or.inr
  by_contra hc
  have hz := gaps_zero_of_two_coordinate_bounds d i
    (lt_of_not_ge h00) (lt_of_not_ge h11) (lt_of_not_ge hc)
  rcases hs with he | hf | hg
  · rw [hz.1] at he
    exact lt_irrefl _ he
  · rw [hz.2.1] at hf
    exact lt_irrefl _ hf
  · rw [hz.2.2] at hg
    exact lt_irrefl _ hg

end CollatzResearch.ForwardRealTwoCoordinateNecessary

#print axioms CollatzResearch.ForwardRealTwoCoordinateNecessary.positive_subeigenrow_of_two_coordinate_bounds
#print axioms CollatzResearch.ForwardRealTwoCoordinateNecessary.gaps_zero_of_two_coordinate_bounds
#print axioms CollatzResearch.ForwardRealTwoCoordinateNecessary.positive_eligible_gap_requires_noncontraction
