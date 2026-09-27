import CollatzReversedRealTriangularSuperunit
import ReversedUpperTriangularRay
import ReversedTriangularTernaryBounds
import CollatzReversedRealTriangularGrowth

namespace CollatzResearch.RealTriangularExpanding

open Matrix CollatzCertificate RealAffine RealOrderedTwo

set_option maxHeartbeats 1000000

theorem strict_upper_expanding_active_diagonal_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha0 : A.matrix 1 0=0) (hb0 : B.matrix 1 0=0) (he0 : E.matrix 1 0=0)
    (hf0 : F.matrix 1 0=0) (hg0 : G.matrix 1 0=0)
    (hfpos : 0<F.matrix 0 0) (ha : 1<A.matrix 0 0) : False := by
  by_cases hb11 : B.matrix 1 1≤1
  swap
  · exact RealTriangularSuperunit.strict_upper_expanding_second_binary_contradiction
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict ha0 hb0 he0 hf0 hg0
        hfpos ha (lt_of_not_ge hb11)
  obtain ⟨hab,hef,hgf,_ha1,_hfpos,hfle⟩ :=
    RealTriangularPositive.positive_active_diagonal_values A B C D E F G i₀ 0 1
      (by decide) hA hB hC hD hE hF hG h hstrict ha0 hb0 he0 hf0 hg0 hfpos
  have ha11 := RealTriangularContracting.strict_upper_second_diagonal_lt_one
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict ha0 hb0
  have hdec := RealOrderedTwo.two_dimensional_binary_product_decrease A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict
  have hlt := RealTriangularNecessity.upper_binary_product_decrease
    A.matrix B.matrix ha0 hb0 hdec
  simp only [Matrix.mul_apply,Fin.sum_univ_two,← hab] at hlt
  have hδ : 0<(A.matrix 0 0-A.matrix 1 1)*B.matrix 0 1-
      (A.matrix 0 0-B.matrix 1 1)*A.matrix 0 1 := by nlinarith only [hlt]
  have hea := h.ea.1 (0 : Fin 2) (1 : Fin 2)
  have hfa := h.fa.1 (0 : Fin 2) (1 : Fin 2)
  have hga := h.ga.1 (0 : Fin 2) (1 : Fin 2)
  have heb := h.eb.1 (0 : Fin 2) (1 : Fin 2)
  have hgb := h.gb.1 (0 : Fin 2) (1 : Fin 2)
  simp only [Affine.comp,Matrix.mul_apply,Fin.sum_univ_two,← hab,hef,hgf] at hea hfa hga heb hgb
  have hdiag := (reversed_swap_equalities_on_diagonal
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
      h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 1).2.2.1
  simp only [Matrix.mul_apply,Fin.sum_univ_two,hg0,ha0,zero_mul,zero_add] at hdiag
  have hdiag' : A.matrix 1 1*G.matrix 1 1=A.matrix 1 1*F.matrix 1 1 := by
    nlinarith only [hdiag]
  obtain ⟨he11,hf11,hg11⟩ := ReversedTriangularTernaryBounds.ternary_secondary_bounds
    (A.matrix 0 0) (A.matrix 1 1) (B.matrix 1 1) (F.matrix 0 0)
    (A.matrix 0 1) (B.matrix 0 1) (E.matrix 1 1) (F.matrix 1 1) (G.matrix 1 1)
    (E.matrix 0 1) (F.matrix 0 1) (G.matrix 0 1)
    (hA.1 1 1) (lt_trans ha11 ha) (lt_of_le_of_lt hb11 ha)
    (hA.1 0 1) (hE.1 0 1) (hF.1 0 1) (hG.1 0 1) (hF.1 1 1)
    hδ hea hfa hga heb hgb hdiag'
  obtain ⟨u,L,hu,hu0,hL,hrate,hEu,hFu,hGu⟩ :=
    ReversedUpperTriangularRay.common_positive_upper_ray E.matrix F.matrix G.matrix
      (A.matrix 0 0) ha hE.1 hF.1 hG.1 he0 hf0 hg0
      (by rw [hef]; exact hfle) hfle (by rw [hgf]; exact hfle)
      (le_trans he11 hfle) (le_trans hf11 hfle) (le_trans hg11 hfle)
  have hb01 : 0<B.matrix 0 1 := by
    by_contra hn
    have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr (lt_trans ha11 ha)).le
      (le_of_not_gt hn)
    have h2 := mul_nonneg (sub_pos.mpr (lt_of_le_of_lt hb11 ha)).le (hA.1 0 1)
    linarith only [hδ,h1,h2]
  have hcross : 0<A.matrix 0 1+B.matrix 0 1 :=
    add_pos_of_nonneg_of_pos (hA.1 0 1) hb01
  have hoff := RealExpandingPrefix.strict_binary_offset_nonzero A B D G i₀ hD hG hstrict
  obtain ⟨p,hp4,hp7,hpnn,hp0⟩ :=
    RealTriangularPrefix.positive_first_binary_prefix_of_nonzero_offset
      A B C.offset hA hB hC.2 (lt_trans zero_lt_one ha) hcross hoff
  exact RealTriangularGrowth.first_coordinate_expanding_contradiction
    A B C D E F G hA hB hC hE hF hG h u (A.matrix 0 0) L
      (ReversedCertificate.binaryInterp (eval A) (eval B) p C.offset 0) p
      hu hu0 ha hL hrate rfl hEu hFu hGu hp4 hp7 hpnn hp0 le_rfl

end CollatzResearch.RealTriangularExpanding

#print axioms CollatzResearch.RealTriangularExpanding.strict_upper_expanding_active_diagonal_contradiction
