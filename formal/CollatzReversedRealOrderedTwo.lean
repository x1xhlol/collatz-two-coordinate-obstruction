import CollatzReversedRealRowContraction
import ReversedSwapRecurrence
import Mathlib.Tactic.FinCases

namespace CollatzResearch.RealOrderedTwo

open Matrix CollatzCertificate RealAffine RealMixedGrowth

theorem sum_two_coordinates (i j : Fin 2) (hne : i ≠ j) (f : Fin 2 → ℝ) :
    ∑ k, f k = f i + f j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_two, add_comm]

theorem two_coordinate_cases (i j k : Fin 2) (hne : i ≠ j) : k = i ∨ k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

set_option maxHeartbeats 4000000 in
theorem ordered_binary_matrices_exclude_two_dimensions
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hBA : EntrywiseLE (A.matrix * B.matrix) (B.matrix * A.matrix)) : False := by
  change (∀ k l, 0 ≤ A.matrix k l) ∧ (∀ k, 0 ≤ A.offset k) at hA
  change (∀ k l, 0 ≤ B.matrix k l) ∧ (∀ k, 0 ≤ B.offset k) at hB
  change (∀ k l, 0 ≤ C.matrix k l) ∧ (∀ k, 0 ≤ C.offset k) at hC
  change (∀ k l, 0 ≤ D.matrix k l) ∧ (∀ k, 0 ≤ D.offset k) at hD
  change (∀ k l, 0 ≤ E.matrix k l) ∧ (∀ k, 0 ≤ E.offset k) at hE
  change (∀ k l, 0 ≤ F.matrix k l) ∧ (∀ k, 0 ≤ F.offset k) at hF
  change (∀ k l, 0 ≤ G.matrix k l) ∧ (∀ k, 0 ≤ G.offset k) at hG
  let r : Vec (Fin 2) := D.matrix i₀
  let q : Vec (Fin 2) := r ᵥ* B.matrix
  have hr : Admissible A.matrix B.matrix G.matrix B.offset G.offset r := by
    refine ⟨fun j => hD.1 i₀ j, ?_, ?_, ?_⟩
    · exact h.da.1 i₀
    · exact h.db.1 i₀
    · have hi := h.db.2 i₀
      change r ⬝ᵥ G.offset + D.offset i₀ ≤ r ⬝ᵥ B.offset + D.offset i₀ at hi
      linarith
  have hrn (k : Fin 2) : 0 ≤ r k := hr.nonneg k
  have hgc : (B.matrix * A.matrix) *ᵥ C.offset + B.matrix *ᵥ A.offset + B.offset ≤
      G.matrix *ᵥ C.offset + G.offset := by
    have hi := h.gc.2
    change B.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + B.offset ≤
      G.matrix *ᵥ C.offset + G.offset at hi
    simpa only [mulVec_add, mulVec_mulVec] using hi
  have hz := admissible_zero_gaps hB.1 hA.2 hC.2 hBA hgc hr
  have hq := rowMul_nonneg hr.nonneg hB.1
  have hqa : q ⬝ᵥ A.offset = 0 := hz.2
  have hrnext := admissible_mul_B hB.1 hB.2 hBA h.gb.1 h.gb.2 hr
  have hqba : (q ᵥ* B.matrix) ⬝ᵥ A.offset = 0 :=
    (admissible_zero_gaps hB.1 hA.2 hC.2 hBA hgc hrnext).2
  have hgap : 0 < r ⬝ᵥ A.offset := by
    rcases hstrict with hs | hs
    · change D.offset i₀ < r ⬝ᵥ A.offset + D.offset i₀ at hs
      linarith
    · change r ⬝ᵥ G.offset + D.offset i₀ < r ⬝ᵥ B.offset + D.offset i₀ at hs
      linarith [hz.1]
  have hFa := first_gap_le_BAa hA.1 hB.1 hF.1 hG.1 hA.2 hE.2 hF.2
    h.ga.1 h.ga.2 h.fa.2 hr hz.2 hz.1.symm
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun k _ => mul_nonneg (hr.nonneg k) (hA.2 k))).mp hgap
  have hri : 0 < r i := by nlinarith only [hi, hrn i, hA.2 i]
  have hai : 0 < A.offset i := by nlinarith only [hi, hrn i, hA.2 i]
  have hqi : q i = 0 := by
    have hp := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hq k) (hA.2 k))).mp hqa i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hp).resolve_right (ne_of_gt hai)
  have hactive : ∃ j, 0 < q j ∧ r j ≤ q j := by
    simpa only [matrixWord, vecMul_one, r, q] using
      RealRowContraction.mixed_word_second_row_nondecrease A B C D E F G i₀
        hA hB hC hD hE hF hG h hstrict []
  obtain ⟨j, hqj, _⟩ := hactive
  have hne : i ≠ j := by intro he; subst j; linarith
  have hs := sum_two_coordinates i j hne
  have hm (M N : Mat (Fin 2)) (l m : Fin 2) :
      (M * N) l m = M l i * N i m + M l j * N j m := hs (fun k => M l k * N k m)
  have hv (M : Mat (Fin 2)) (v : Vec (Fin 2)) (l : Fin 2) :
      (M *ᵥ v) l = M l i * v i + M l j * v j := hs (fun k => M l k * v k)
  have hw (v : Vec (Fin 2)) (M : Mat (Fin 2)) (l : Fin 2) :
      (v ᵥ* M) l = v i * M i l + v j * M j l := hs (fun k => v k * M k l)
  have hd (v w : Vec (Fin 2)) : v ⬝ᵥ w = v i * w i + v j * w j := hs (fun k => v k * w k)
  have haj : A.offset j = 0 := by
    rw [hd, hqi, zero_mul, zero_add] at hqa
    exact (mul_eq_zero.mp hqa).resolve_left (ne_of_gt hqj)
  have hbii : B.matrix i i = 0 := by
    have he : q i = r i * B.matrix i i + r j * B.matrix j i := hw r B.matrix i
    nlinarith only [he, hqi, hri, hrn j, hB.1 i i, hB.1 j i]
  have hbji : B.matrix j i = 0 := by
    rw [hd, hw, hqi, haj] at hqba
    simp only [zero_mul, zero_add] at hqba
    have hp : 0 < q j * A.offset i := mul_pos hqj hai
    nlinarith only [hqba, hp, hB.1 j i]
  have hreturn : ∃ k, 0 < (q ᵥ* B.matrix) k ∧ q k ≤ (q ᵥ* B.matrix) k := by
    simpa only [matrixWord, affineDigit, Matrix.mul_one, r, q] using
      RealRowContraction.mixed_word_second_row_nondecrease A B C D E F G i₀
        hA hB hC hD hE hF hG h hstrict [.b]
  have hLam : 1 ≤ B.matrix j j := by
    obtain ⟨k, hk, hle⟩ := hreturn
    have hcover : k = i ∨ k = j := two_coordinate_cases i j k hne
    rcases hcover with rfl | rfl
    · rw [hw, hqi, hbji] at hk
      simp at hk
    · rw [hw, hqi, zero_mul, zero_add] at hle
      nlinarith only [hle, hqj]
  have hajipos : 0 < A.matrix j i := by
    have ht : 0 < (q ᵥ* A.matrix) ⬝ᵥ A.offset := by
      simpa only [q, ← vecMul_vecMul] using lt_of_lt_of_le hgap hFa
    rw [hd, hw, hqi, haj] at ht
    simp only [zero_mul, zero_add, mul_zero, add_zero] at ht
    by_contra hn
    have he : A.matrix j i = 0 := le_antisymm (le_of_not_gt hn) (hA.1 j i)
    rw [he, mul_zero, zero_mul] at ht
    exact (lt_irrefl 0) ht
  have hbij : B.matrix i j = 0 := by
    have ht := hBA j j
    rw [hm, hm, hbji] at ht
    nlinarith only [ht, hajipos, hB.1 i j]
  have haij : A.matrix i j = 0 := by
    have ht := hBA i j
    rw [hm, hm, hbii, hbij] at ht
    nlinarith only [ht, hLam, hA.1 i j]
  have hrj : 0 < r j := by
    have ht : q j = r i * B.matrix i j + r j * B.matrix j j := hw r B.matrix j
    rw [hbij] at ht
    nlinarith only [ht, hqj, hrn j, hB.1 j j]
  have hajj : 1 ≤ A.matrix j j := by
    have ht := hr.da j
    rw [hw, haij] at ht
    nlinarith only [ht, hrj]
  have diag (k : Fin 2) := reversed_swap_equalities_on_diagonal
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
    h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 k
  have hfij : F.matrix i j = 0 := by
    have ht := (diag i).2.1
    rw [hm, hm, hbii, hbij] at ht
    nlinarith only [ht, hajipos, hF.1 i i, hA.1 i i, hF.1 i j]
  have hfji : F.matrix j i = 0 := by
    have ht := h.eb.1 j i
    change (B.matrix * F.matrix) j i ≤ (E.matrix * B.matrix) j i at ht
    rw [hm, hm, hbii, hbji] at ht
    nlinarith only [ht, hLam, hF.1 j i]
  have hgii : G.matrix i i = 0 := by
    have ht := h.fb.1 j i
    change (A.matrix * G.matrix) j i ≤ (F.matrix * B.matrix) j i at ht
    rw [hm, hm, hbii, hbji] at ht
    nlinarith only [ht, hajipos, hajj, hG.1 i i, hG.1 j i]
  have hgji : G.matrix j i = 0 := by
    have ht := h.fb.1 j i
    change (A.matrix * G.matrix) j i ≤ (F.matrix * B.matrix) j i at ht
    rw [hm, hm, hbii, hbji, hgii] at ht
    nlinarith only [ht, hajj, hG.1 j i]
  have hfiiaii : F.matrix i i * A.matrix i i = 0 := by
    have ht := (diag i).2.1
    simpa only [hm, hfij, hbii, hbij, zero_mul, mul_zero, add_zero] using ht
  have hgij : G.matrix i j = 0 := by
    have ht := (diag i).2.2.1
    rw [hm, hm, hgii, hfji] at ht
    nlinarith only [ht, hfiiaii, hajipos, hG.1 i j]
  have heij : E.matrix i j = 0 := by
    have ht := (diag i).1
    rw [hm, hm, haij] at ht
    nlinarith only [ht, hajipos, hE.1 i j]
  have hef : E.matrix j j = F.matrix j j := by
    have ht := (diag j).2.2.2.1
    rw [hm, hm, hbji, hbij] at ht
    nlinarith only [ht, hLam]
  have hgf : G.matrix j j = F.matrix j j := by
    have ht := (diag j).2.2.1
    rw [hm, hm, hgji, hfij] at ht
    nlinarith only [ht, hajj]
  have hμLam : F.matrix j j ≤ B.matrix j j := by
    have ht := hr.dbMatrix j
    rw [hw, hw, hgij, hbij, hgf] at ht
    nlinarith only [ht, hrj]
  have hgapFa : r ⬝ᵥ A.offset ≤ (r ᵥ* F.matrix) ⬝ᵥ A.offset := by
    have hGa : (r ᵥ* G.matrix) ⬝ᵥ A.offset = 0 := by
      have hu := dotProduct_le_dotProduct_of_nonneg_right hr.dbMatrix hA.2
      have hl := dotProduct_nonneg_of_nonneg (rowMul_nonneg hr.nonneg hG.1) hA.2
      rw [hz.2] at hu
      exact le_antisymm hu hl
    have hfa := dotProduct_le_dotProduct_of_nonneg_left h.fa.2 hr.nonneg
    have hga := dotProduct_le_dotProduct_of_nonneg_left h.ga.2 hr.nonneg
    have hAf := dotProduct_le_dotProduct_of_nonneg_right hr.da hF.2
    have hBe := dotProduct_nonneg_of_nonneg (rowMul_nonneg hr.nonneg hB.1) hE.2
    change r ⬝ᵥ (B.matrix *ᵥ E.offset + B.offset) ≤
      r ⬝ᵥ (F.matrix *ᵥ A.offset + F.offset) at hfa
    change r ⬝ᵥ (A.matrix *ᵥ F.offset + A.offset) ≤
      r ⬝ᵥ (G.matrix *ᵥ A.offset + G.offset) at hga
    simp only [dotProduct_add, dotProduct_mulVec] at hfa hga
    linarith only [hfa, hga, hAf, hBe, hGa, hz.1]
  have hFii : 0 < F.matrix i i := by
    have ht := hgapFa
    rw [hd, hd, hw, hfji, haj] at ht
    simp only [mul_zero, add_zero] at ht
    have hp : 0 < r i * A.offset i := mul_pos hri hai
    by_contra hn
    have he : F.matrix i i = 0 := le_antisymm (le_of_not_gt hn) (hF.1 i i)
    rw [he] at ht
    simp only [mul_zero, zero_mul] at ht
    linarith only [ht, hp]
  have hμpos : 0 < F.matrix j j := by
    have ht := h.ga.1 j i
    change (A.matrix * F.matrix) j i ≤ (G.matrix * A.matrix) j i at ht
    rw [hm, hm, hfji, hgji, hgf] at ht
    nlinarith only [ht, hajipos, hFii, hF.1 j j]
  have hajjLam : A.matrix j j = B.matrix j j := by
    have ht := (diag j).2.1
    rw [hm, hm, hfji, hbji, hef] at ht
    nlinarith only [ht, hμpos]
  have hgcj := hgc j
  have hgci := hgc i
  have hLamμ : 0 ≤ B.matrix j j * B.matrix j j - F.matrix j j := by nlinarith only [hLam, hμLam]
  simp only [Pi.add_apply, hv, hm, hbii, hbji, hbij, haij, hgii, hgji, hgij,
    hgf, haj, hajjLam, zero_mul, mul_zero, zero_add, add_zero] at hgcj hgci
  have hgj : B.offset j ≤ G.offset j := by
    nlinarith only [hgcj, hC.2 i, hC.2 j, mul_nonneg hLamμ (hC.2 j),
      mul_nonneg (mul_nonneg (hB.1 j j) (hA.1 j i)) (hC.2 i)]
  have hgi : B.offset i ≤ G.offset i := by simpa using hgci
  have hbg := hz.1
  rw [hd, hd] at hbg
  have hgbi : G.offset i = B.offset i := by nlinarith only [hbg, hgj, hgi, hri, hrj]
  have hgbj : G.offset j = B.offset j := by nlinarith only [hbg, hgj, hgi, hri, hrj]
  have hγi : C.offset i = 0 := by
    rw [hgbj] at hgcj
    have hp : 0 < B.matrix j j * A.matrix j i := mul_pos (by linarith only [hLam]) hajipos
    nlinarith only [hgcj, hp, hC.2 i, mul_nonneg hLamμ (hC.2 j)]
  have hfa := h.fa.2 j
  have hga := h.ga.2 j
  change (B.matrix *ᵥ E.offset) j + B.offset j ≤ (F.matrix *ᵥ A.offset) j + F.offset j at hfa
  change (A.matrix *ᵥ F.offset) j + A.offset j ≤ (G.matrix *ᵥ A.offset) j + G.offset j at hga
  simp only [hv, hbji, hfji, hgji, haj, hgf, hajjLam, hgbj,
    zero_mul, mul_zero, zero_add, add_zero] at hfa hga
  have hfj : F.offset j = B.offset j := by nlinarith only [hfa, hga, hLam, hajipos, hE.2 j, hF.2 i, hF.2 j]
  have hej : E.offset j = 0 := by rw [hfj] at hfa; nlinarith only [hfa, hLam, hE.2 j]
  have hec := h.ec.2 j
  change (B.matrix *ᵥ C.offset) j + B.offset j ≤ (E.matrix *ᵥ C.offset) j + E.offset j at hec
  simp only [hv, hbji, hγi, hej, hef, mul_zero, zero_add, add_zero] at hec
  have hbj : B.offset j = 0 := by nlinarith only [hec, hμLam, hC.2 j, hB.2 j]
  have hfb := h.fb.2 j
  change (A.matrix *ᵥ G.offset) j + A.offset j ≤ (F.matrix *ᵥ B.offset) j + F.offset j at hfb
  simp only [hv, hfji, haj, hfj, hgbj, hbj, zero_mul, mul_zero, add_zero] at hfb
  have hgi0 : G.offset i = 0 := by nlinarith only [hfb, hajipos, hG.2 i]
  have hgai := h.ga.2 i
  change (A.matrix *ᵥ F.offset) i + A.offset i ≤ (G.matrix *ᵥ A.offset) i + G.offset i at hgai
  simp only [hv, hgii, hgij, hgi0, zero_mul, zero_add] at hgai
  nlinarith only [hgai, hai, mul_nonneg (hA.1 i i) (hF.2 i),
    mul_nonneg (hA.1 i j) (hF.2 j)]

theorem two_dimensional_ordered_gaps_zero
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hBA : EntrywiseLE (A.matrix * B.matrix) (B.matrix * A.matrix)) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  have hn := ordered_binary_matrices_exclude_two_dimensions A B C D E F G i₀
    hA hB hC hD hE hF hG h
  constructor
  · apply le_antisymm _ (h.da.2 i₀)
    by_contra hp
    exact hn (Or.inl (lt_of_not_ge hp)) hBA
  · apply le_antisymm _ (h.db.2 i₀)
    by_contra hp
    exact hn (Or.inr (lt_of_not_ge hp)) hBA

theorem two_dimensional_binary_product_decrease
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ i j, (B.matrix * A.matrix) i j < (A.matrix * B.matrix) i j := by
  by_contra hn
  apply ordered_binary_matrices_exclude_two_dimensions A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict
  intro i j
  by_contra hp
  exact hn ⟨i, j, lt_of_not_ge hp⟩

#print axioms sum_two_coordinates
#print axioms two_coordinate_cases
#print axioms ordered_binary_matrices_exclude_two_dimensions
#print axioms two_dimensional_ordered_gaps_zero
#print axioms two_dimensional_binary_product_decrease

end CollatzResearch.RealOrderedTwo
