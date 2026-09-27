import CollatzReversedRealPositiveWord

namespace CollatzResearch.RealRowContraction

open Matrix CollatzCertificate RealAffine RealMixedGrowth

variable {ι : Type*} [Fintype ι]

theorem contracting_row_iterates_bounded (A : Affine ι) (q γ : Vec ι) (β : ℝ)
    (hA : A.Nonnegative) (hq : 0 ≤ q) (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (hβone : β < 1)
    (hrow : q ᵥ* A.matrix ≤ β • q) :
    ∃ L : ℝ, ∀ n : ℕ, q ⬝ᵥ ((eval A)^[n] γ) ≤ L := by
  let L := q ⬝ᵥ γ + (q ⬝ᵥ A.offset) / (1 - β)
  have hden : 0 < 1 - β := sub_pos.mpr hβone
  have hqγ := dotProduct_nonneg_of_nonneg hq hγ
  have hqa := dotProduct_nonneg_of_nonneg hq hA.2
  have hbase : q ⬝ᵥ γ ≤ L := by
    dsimp [L]
    linarith [div_nonneg hqa hden.le]
  have hstep : β * L + q ⬝ᵥ A.offset ≤ L := by
    have heq := div_mul_cancel₀ (q ⬝ᵥ A.offset) (ne_of_gt hden)
    dsimp [L]
    nlinarith
  have hn (n : ℕ) : 0 ≤ (eval A)^[n] γ := by
    induction n with
    | zero => exact hγ
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact eval_nonnegative hA ih
  refine ⟨L, ?_⟩
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change q ⬝ᵥ (A.matrix *ᵥ ((eval A)^[n] γ) + A.offset) ≤ L
    rw [dotProduct_add, dotProduct_mulVec]
    have hle := dotProduct_le_dotProduct_of_nonneg_right hrow (hn n)
    rw [smul_dotProduct] at hle
    have hmul := mul_le_mul_of_nonneg_left ih hβ
    change (q ᵥ* A.matrix) ⬝ᵥ ((eval A)^[n] γ) ≤ β * (q ⬝ᵥ ((eval A)^[n] γ)) at hle
    linarith

theorem row_contraction_of_no_active_nondecrease [Nonempty ι]
    (M : Mat ι) (q : Vec ι) (hM : EntrywiseLE 0 M) (hq : 0 ≤ q)
    (hn : ¬ ∃ j, 0 < (q ᵥ* M) j ∧ q j ≤ (q ᵥ* M) j) :
    ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ q ᵥ* M ≤ β • q := by
  classical
  have hqM := rowMul_nonneg hq hM
  have hz (j : ι) (hj : q j = 0) : (q ᵥ* M) j = 0 := by
    apply le_antisymm _ (hqM j)
    by_contra hp
    exact hn ⟨j, lt_of_not_ge hp, by rw [hj]; exact hqM j⟩
  let t : ι → ℝ := fun j => if q j = 0 then 0 else (q ᵥ* M) j / q j
  have htzero (j : ι) : 0 ≤ t j := by
    dsimp [t]
    split
    · exact le_rfl
    · exact div_nonneg (hqM j) (hq j)
  have htone (j : ι) : t j < 1 := by
    by_cases hj : q j = 0
    · simp [t, hj]
    · have hp : 0 < q j := lt_of_le_of_ne (hq j) (Ne.symm hj)
      have hlt : (q ᵥ* M) j < q j := by
        by_contra hle
        exact hn ⟨j, hp.trans_le (le_of_not_gt hle), le_of_not_gt hle⟩
      simpa only [t, hj, ↓reduceIte, div_lt_one hp] using hlt
  let β := Finset.univ.sup' Finset.univ_nonempty t
  have ht (j : ι) : t j ≤ β := Finset.le_sup' t (Finset.mem_univ j)
  refine ⟨β, (htzero (Classical.arbitrary ι)).trans (ht _), ?_, ?_⟩
  · exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun j _ => htone j)
  · intro j
    by_cases hj : q j = 0
    · change (q ᵥ* M) j ≤ β * q j
      rw [hj, hz j hj, mul_zero]
    · have hp : 0 < q j := lt_of_le_of_ne (hq j) (Ne.symm hj)
      have hi : (q ᵥ* M) j / q j ≤ β := by simpa only [t, hj, ↓reduceIte] using ht j
      exact (div_le_iff₀ hp).mp hi

theorem unbounded_row_has_active_nondecrease [Nonempty ι]
    (A : Affine ι) (q γ : Vec ι) (hA : A.Nonnegative) (hq : 0 ≤ q) (hγ : 0 ≤ γ)
    (hgrowth : ∀ K : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < q ⬝ᵥ ((eval A)^[n] γ)) :
    ∃ j, 0 < (q ᵥ* A.matrix) j ∧ q j ≤ (q ᵥ* A.matrix) j := by
  by_contra hn
  obtain ⟨β, hβ, hβone, hrow⟩ := row_contraction_of_no_active_nondecrease A.matrix q hA.1 hq hn
  obtain ⟨L, hL⟩ := contracting_row_iterates_bounded A q γ β hA hq hγ hβ hβone hrow
  obtain ⟨N, hN⟩ := hgrowth L
  exact (not_lt_of_ge (hL N)) (hN N le_rfl)

theorem unbounded_row_has_offset_or_increase
    (A : Affine ι) (q γ : Vec ι) (hA : A.Nonnegative) (hγ : 0 ≤ γ)
    (hgrowth : ∀ K : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < q ⬝ᵥ ((eval A)^[n] γ)) :
    0 < q ⬝ᵥ A.offset ∨ ∃ j, q j < (q ᵥ* A.matrix) j := by
  by_contra hn
  have ha : q ⬝ᵥ A.offset ≤ 0 := by
    by_contra hp
    exact hn (Or.inl (lt_of_not_ge hp))
  have hrow : q ᵥ* A.matrix ≤ q := by
    intro j
    by_contra hp
    exact hn (Or.inr ⟨j, lt_of_not_ge hp⟩)
  have hnonnegative (n : ℕ) : 0 ≤ (eval A)^[n] γ := by
    induction n with
    | zero => exact hγ
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact eval_nonnegative hA ih
  have hbound (n : ℕ) : q ⬝ᵥ ((eval A)^[n] γ) ≤ q ⬝ᵥ γ := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change q ⬝ᵥ (A.matrix *ᵥ ((eval A)^[n] γ) + A.offset) ≤ q ⬝ᵥ γ
      rw [dotProduct_add, dotProduct_mulVec]
      have hi := dotProduct_le_dotProduct_of_nonneg_right hrow (hnonnegative n)
      linarith
  obtain ⟨N, hN⟩ := hgrowth (q ⬝ᵥ γ)
  exact (not_lt_of_ge (hbound N)) (hN N le_rfl)

variable [DecidableEq ι]

theorem mixed_word_second_row_nondecrease
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) (w : List MixedSupport.Digit) :
    ∃ j, 0 < ((D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ᵥ* B.matrix) j ∧
      (D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) j ≤
        ((D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ᵥ* B.matrix) j := by
  letI : Nonempty ι := ⟨i₀⟩
  have hm : ∀ k, EntrywiseLE 0 (affineDigit A B E F G k).matrix := by
    intro k
    cases k
    · exact hA.1
    · exact hB.1
    · exact hE.1
    · exact hF.1
    · exact hG.1
  apply unbounded_row_has_active_nondecrease B _ C.offset hB
    (rowMul_nonneg (fun j => hD.1 i₀ j) (matrixWord_nonnegative _ hm w)) hC.2
  exact real_reversed_mixed_row_growth A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict w

theorem positive_word_first_row_nondecrease
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List MixedSupport.Digit) (hw : 0 < MixedSupport.label w 0) :
    ∃ j, 0 < ((D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ᵥ* A.matrix) j ∧
      (D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) j ≤
        ((D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ᵥ* A.matrix) j := by
  letI : Nonempty ι := ⟨i₀⟩
  have hm : ∀ k, EntrywiseLE 0 (affineDigit A B E F G k).matrix := by
    intro k
    cases k
    · exact hA.1
    · exact hB.1
    · exact hE.1
    · exact hF.1
    · exact hG.1
  apply unbounded_row_has_active_nondecrease A _ C.offset hA
    (rowMul_nonneg (fun j => hD.1 i₀ j) (matrixWord_nonnegative _ hm w)) hC.2
  exact RealPositiveWord.real_positive_word_row_growth A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict w hw

#print axioms contracting_row_iterates_bounded
#print axioms row_contraction_of_no_active_nondecrease
#print axioms unbounded_row_has_active_nondecrease
#print axioms unbounded_row_has_offset_or_increase
#print axioms mixed_word_second_row_nondecrease
#print axioms positive_word_first_row_nondecrease

end CollatzResearch.RealRowContraction
