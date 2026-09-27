import ReversedTwoDimensionalSwapAlgebra
import CollatzReversedRealRowContraction

namespace CollatzResearch.RealCommutatorTwo

open Matrix CollatzCertificate RealAffine RealMixedGrowth TwoDimensionalSwapAlgebra

theorem weak_swaps_middle_nonzero_force_singular_commutator (A B E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hea : EntrywiseLE (A * E) (E * A))
    (hfa : EntrywiseLE (B * E) (F * A))
    (hga : EntrywiseLE (A * F) (G * A))
    (heb : EntrywiseLE (B * F) (E * B))
    (hfb : EntrywiseLE (A * G) (F * B))
    (hgb : EntrywiseLE (B * G) (G * B)) (hFn : F ≠ 0) : delta A B = 0 := by
  change ∀ i j, 0 ≤ A i j at hA
  change ∀ i j, 0 ≤ B i j at hB
  change ∀ i j, 0 ≤ E i j at hE
  change ∀ i j, 0 ≤ F i j at hF
  change ∀ i j, 0 ≤ G i j at hG
  by_contra hd
  let H := (A + B) + (E + F + G)
  have h01 : 0 < H 0 1 := by
    by_contra hn
    have hh : H 0 1 ≤ 0 := le_of_not_gt hn
    change A 0 1 + B 0 1 + (E 0 1 + F 0 1 + G 0 1) ≤ 0 at hh
    have ha : A 0 1 = 0 := by
      linarith only [hh, hA 0 1, hB 0 1, hE 0 1, hF 0 1, hG 0 1]
    have hb : B 0 1 = 0 := by
      linarith only [hh, hA 0 1, hB 0 1, hE 0 1, hF 0 1, hG 0 1]
    apply hd
    simp only [delta, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two, ha, hb]
    ring
  have h10 : 0 < H 1 0 := by
    by_contra hn
    have hh : H 1 0 ≤ 0 := le_of_not_gt hn
    change A 1 0 + B 1 0 + (E 1 0 + F 1 0 + G 1 0) ≤ 0 at hh
    have ha : A 1 0 = 0 := by
      linarith only [hh, hA 1 0, hB 1 0, hE 1 0, hF 1 0, hG 1 0]
    have hb : B 1 0 = 0 := by
      linarith only [hh, hA 1 0, hB 1 0, hE 1 0, hF 1 0, hG 1 0]
    apply hd
    simp only [delta, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two, ha, hb]
    ring
  have hreturn : ∀ i j : Fin 2, ∃ k : ℕ, 0 < (H ^ k) j i := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simpa only [pow_one] using h10⟩
    · exact ⟨1, by simpa only [pow_one] using h01⟩
    · exact ⟨0, by simp⟩
  obtain ⟨he, hf, hg, heb', hfb', hgb'⟩ := reversed_swap_equalities_of_all_returns
    A B E F G hA hB hE hF hG hea hfa hga heb hfb hgb hreturn
  exact hFn (exact_swaps_force_middle_zero A B E F G
    (add_nonneg (hA 0 0) (hA 1 1)) (add_nonneg (hB 0 0) (hB 1 1))
    hd he hf hg heb' hfb' hgb')

theorem strict_reversed_middle_matrix_nonzero
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) : F.matrix ≠ 0 := by
  intro hz
  obtain ⟨j, hj, _⟩ := RealRowContraction.mixed_word_second_row_nondecrease
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict [.f]
  simp [matrixWord, affineDigit, hz] at hj

theorem strict_reversed_binary_commutator_singular
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    (A.matrix * B.matrix - B.matrix * A.matrix).det = 0 := by
  exact weak_swaps_middle_nonzero_force_singular_commutator
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
    h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1
    (strict_reversed_middle_matrix_nonzero A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict)

end CollatzResearch.RealCommutatorTwo

#print axioms CollatzResearch.RealCommutatorTwo.weak_swaps_middle_nonzero_force_singular_commutator
#print axioms CollatzResearch.RealCommutatorTwo.strict_reversed_middle_matrix_nonzero
#print axioms CollatzResearch.RealCommutatorTwo.strict_reversed_binary_commutator_singular
