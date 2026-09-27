import CollatzReversedRealAllReturns

namespace CollatzResearch.RealTriangularNecessity

open Matrix CollatzCertificate RealAffine

theorem missing_return_zero_offdiagonal (H : Mat (Fin 2))
    (hH : EntrywiseLE 0 H)
    (hn : ¬ ∀ i j : Fin 2, ∃ k : ℕ, 0 < (H^k) j i) : H 0 1=0 ∨ H 1 0=0 := by
  by_cases h01 : H 0 1=0
  · exact Or.inl h01
  right
  by_contra h10
  have hp01 : 0 < H 0 1 := lt_of_le_of_ne (hH 0 1) (Ne.symm h01)
  have hp10 : 0 < H 1 0 := lt_of_le_of_ne (hH 1 0) (Ne.symm h10)
  apply hn
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simpa only [pow_one] using hp10⟩
  · exact ⟨1,by simpa only [pow_one] using hp01⟩
  · exact ⟨0,by simp⟩

theorem five_nonnegative_zero_entry (A B E F G : Mat (Fin 2)) (i j : Fin 2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hE : EntrywiseLE 0 E) (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hz : ((A+B)+(E+F+G)) i j=0) :
    A i j=0 ∧ B i j=0 ∧ E i j=0 ∧ F i j=0 ∧ G i j=0 := by
  have ha : 0 ≤ A i j := hA i j
  have hb : 0 ≤ B i j := hB i j
  have he : 0 ≤ E i j := hE i j
  have hf : 0 ≤ F i j := hF i j
  have hg : 0 ≤ G i j := hG i j
  change A i j+B i j+(E i j+F i j+G i j)=0 at hz
  constructor
  · linarith only [hz,ha,hb,he,hf,hg]
  constructor
  · linarith only [hz,ha,hb,he,hf,hg]
  constructor
  · linarith only [hz,ha,hb,he,hf,hg]
  constructor <;> linarith only [hz,ha,hb,he,hf,hg]

theorem upper_binary_product_decrease (A B : Mat (Fin 2))
    (ha : A 1 0=0) (hb : B 1 0=0)
    (hdec : ∃ i j, (B*A) i j < (A*B) i j) : (B*A) 0 1 < (A*B) 0 1 := by
  obtain ⟨i,j,hij⟩ := hdec
  fin_cases i <;> fin_cases j
  · change (B*A) 0 0 < (A*B) 0 0 at hij
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,add_zero,mul_comm,
      lt_self_iff_false] at hij
  · exact hij
  · change (B*A) 1 0 < (A*B) 1 0 at hij
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,mul_zero,zero_mul,add_zero,
      lt_self_iff_false] at hij
  · change (B*A) 1 1 < (A*B) 1 1 at hij
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,zero_add,mul_comm,
      lt_self_iff_false] at hij

theorem lower_binary_product_decrease (A B : Mat (Fin 2))
    (ha : A 0 1=0) (hb : B 0 1=0)
    (hdec : ∃ i j, (B*A) i j < (A*B) i j) : (B*A) 1 0 < (A*B) 1 0 := by
  obtain ⟨i,j,hij⟩ := hdec
  fin_cases i <;> fin_cases j
  · change (B*A) 0 0 < (A*B) 0 0 at hij
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,add_zero,mul_comm,
      lt_self_iff_false] at hij
  · change (B*A) 0 1 < (A*B) 0 1 at hij
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,mul_zero,zero_mul,add_zero,
      lt_self_iff_false] at hij
  · exact hij
  · change (B*A) 1 1 < (A*B) 1 1 at hij
    simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,zero_add,mul_comm,
      lt_self_iff_false] at hij

theorem strict_reversed_common_triangular_orientation
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    (A.matrix 1 0=0 ∧ B.matrix 1 0=0 ∧ E.matrix 1 0=0 ∧
      F.matrix 1 0=0 ∧ G.matrix 1 0=0 ∧
      (B.matrix*A.matrix) 0 1 < (A.matrix*B.matrix) 0 1) ∨
    (A.matrix 0 1=0 ∧ B.matrix 0 1=0 ∧ E.matrix 0 1=0 ∧
      F.matrix 0 1=0 ∧ G.matrix 0 1=0 ∧
      (B.matrix*A.matrix) 1 0 < (A.matrix*B.matrix) 1 0) := by
  have hn : ¬ ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix))^k) j i := by
    intro hr
    exact RealAllReturns.strict_reversed_all_returns_contradiction A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict hr
  have hH : EntrywiseLE 0 ((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix)) := fun i j =>
    add_nonneg (add_nonneg (hA.1 i j) (hB.1 i j))
      (add_nonneg (add_nonneg (hE.1 i j) (hF.1 i j)) (hG.1 i j))
  have hdec := RealOrderedTwo.two_dimensional_binary_product_decrease A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict
  rcases missing_return_zero_offdiagonal _ hH hn with h01 | h10
  · obtain ⟨ha,hb,he,hf,hg⟩ := five_nonnegative_zero_entry
      A.matrix B.matrix E.matrix F.matrix G.matrix 0 1 hA.1 hB.1 hE.1 hF.1 hG.1 h01
    exact Or.inr ⟨ha,hb,he,hf,hg,lower_binary_product_decrease A.matrix B.matrix ha hb hdec⟩
  · obtain ⟨ha,hb,he,hf,hg⟩ := five_nonnegative_zero_entry
      A.matrix B.matrix E.matrix F.matrix G.matrix 1 0 hA.1 hB.1 hE.1 hF.1 hG.1 h10
    exact Or.inl ⟨ha,hb,he,hf,hg,upper_binary_product_decrease A.matrix B.matrix ha hb hdec⟩

theorem strict_reversed_reverse_ordered_binary_products
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    EntrywiseLE (B.matrix*A.matrix) (A.matrix*B.matrix) ∧
      B.matrix*A.matrix ≠ A.matrix*B.matrix := by
  rcases strict_reversed_common_triangular_orientation A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict with
    ⟨ha,hb,_he,_hf,_hg,hlt⟩ | ⟨ha,hb,_he,_hf,_hg,hlt⟩
  · constructor
    · intro i j
      fin_cases i <;> fin_cases j
      · change (B.matrix*A.matrix) 0 0 ≤ (A.matrix*B.matrix) 0 0
        simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,add_zero,mul_comm,le_refl]
      · exact hlt.le
      · change (B.matrix*A.matrix) 1 0 ≤ (A.matrix*B.matrix) 1 0
        simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,mul_zero,zero_mul,add_zero,le_refl]
      · change (B.matrix*A.matrix) 1 1 ≤ (A.matrix*B.matrix) 1 1
        simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,zero_add,mul_comm,le_refl]
    · intro heq
      rw [heq] at hlt
      exact (lt_irrefl _) hlt
  · constructor
    · intro i j
      fin_cases i <;> fin_cases j
      · change (B.matrix*A.matrix) 0 0 ≤ (A.matrix*B.matrix) 0 0
        simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,add_zero,mul_comm,le_refl]
      · change (B.matrix*A.matrix) 0 1 ≤ (A.matrix*B.matrix) 0 1
        simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,mul_zero,zero_mul,add_zero,le_refl]
      · exact hlt.le
      · change (B.matrix*A.matrix) 1 1 ≤ (A.matrix*B.matrix) 1 1
        simp only [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,zero_mul,zero_add,mul_comm,le_refl]
    · intro heq
      rw [heq] at hlt
      exact (lt_irrefl _) hlt

end CollatzResearch.RealTriangularNecessity

#print axioms CollatzResearch.RealTriangularNecessity.missing_return_zero_offdiagonal
#print axioms CollatzResearch.RealTriangularNecessity.five_nonnegative_zero_entry
#print axioms CollatzResearch.RealTriangularNecessity.upper_binary_product_decrease
#print axioms CollatzResearch.RealTriangularNecessity.lower_binary_product_decrease
#print axioms CollatzResearch.RealTriangularNecessity.strict_reversed_common_triangular_orientation
#print axioms CollatzResearch.RealTriangularNecessity.strict_reversed_reverse_ordered_binary_products
