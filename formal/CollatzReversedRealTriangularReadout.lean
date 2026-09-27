import CollatzReversedRealTriangularNecessity

namespace CollatzResearch.RealTriangularReadout

open Matrix CollatzCertificate RealAffine RealOrderedTwo

theorem strict_triangular_second_row_positive
    (A B C D E F G : Affine (Fin 2)) (i₀ i j : Fin 2) (hne : i ≠ j)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hazero : A.matrix j i=0) : 0 < (D.matrix i₀ ᵥ* B.matrix) i := by
  let q : Vec (Fin 2) := D.matrix i₀ ᵥ* B.matrix
  have hq : 0 ≤ q := rowMul_nonneg (fun k => hD.1 i₀ k) hB.1
  by_contra hn
  have hqi : q i=0 := le_antisymm (le_of_not_gt hn) (hq i)
  have heigen : q ᵥ* A.matrix=A.matrix j j • q := by
    funext k
    change (∑ l, q l*A.matrix l k)=A.matrix j j*q k
    rw [sum_two_coordinates i j hne]
    rcases two_coordinate_cases i j k hne with rfl | rfl
    · rw [hqi,hazero,zero_mul,mul_zero,add_zero,mul_zero]
    · rw [hqi,zero_mul,zero_add,mul_comm]
  exact RealAbovePowers.real_second_row_not_first_eigenrow A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict (A.matrix j j) (hA.1 j j) heigen

theorem strict_triangular_active_diagonal_bounds
    (A B C D E F G : Affine (Fin 2)) (i₀ i j : Fin 2) (hne : i ≠ j)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hazero : A.matrix j i=0) (hbzero : B.matrix j i=0) :
    0 < D.matrix i₀ i ∧ 1 ≤ A.matrix i i ∧ 0 < B.matrix i i ∧
      G.matrix i i ≤ B.matrix i i := by
  have hqi := strict_triangular_second_row_positive A B C D E F G i₀ i j hne
    hA hB hC hD hE hF hG h hstrict hazero
  change 0 < ∑ k, D.matrix i₀ k*B.matrix k i at hqi
  rw [sum_two_coordinates i j hne,hbzero,mul_zero,add_zero] at hqi
  have hr : 0 < D.matrix i₀ i := by
    have hn : 0 ≤ D.matrix i₀ i := hD.1 i₀ i
    have hb : 0 ≤ B.matrix i i := hB.1 i i
    nlinarith only [hqi,hn,hb]
  have hb : 0 < B.matrix i i := by
    have hn : 0 ≤ D.matrix i₀ i := hD.1 i₀ i
    have hb : 0 ≤ B.matrix i i := hB.1 i i
    nlinarith only [hqi,hn,hb]
  have hda := h.da.1 i₀ i
  change D.matrix i₀ i ≤ ∑ k, D.matrix i₀ k*A.matrix k i at hda
  rw [sum_two_coordinates i j hne,hazero,mul_zero,add_zero] at hda
  have ha : 1 ≤ A.matrix i i := by nlinarith only [hda,hr]
  have hdb := h.db.1 i₀ i
  change (∑ k, D.matrix i₀ k*G.matrix k i) ≤ ∑ k, D.matrix i₀ k*B.matrix k i at hdb
  rw [sum_two_coordinates i j hne,sum_two_coordinates i j hne,hbzero,mul_zero,add_zero] at hdb
  have hx : 0 ≤ D.matrix i₀ j*G.matrix j i := mul_nonneg (hD.1 i₀ j) (hG.1 j i)
  refine ⟨hr,ha,hb,?_⟩
  nlinarith only [hdb,hx,hr]

end CollatzResearch.RealTriangularReadout

#print axioms CollatzResearch.RealTriangularReadout.strict_triangular_second_row_positive
#print axioms CollatzResearch.RealTriangularReadout.strict_triangular_active_diagonal_bounds
