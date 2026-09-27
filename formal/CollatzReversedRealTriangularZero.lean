import CollatzReversedRealTriangularZeroBasic

namespace CollatzResearch.RealTriangularZero

open Matrix CollatzCertificate RealAffine RealTriangularZeroBasic

set_option maxHeartbeats 1000000

theorem strict_upper_zero_middle_diagonal_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hA10 : A.matrix 1 0=0) (hB10 : B.matrix 1 0=0)
    (hE10 : E.matrix 1 0=0) (hF10 : F.matrix 1 0=0) (hG10 : G.matrix 1 0=0)
    (hF00 : F.matrix 0 0=0) : False := by
  obtain ⟨_hr,hA00,hB00,_hGbound⟩ :=
    RealTriangularReadout.strict_triangular_active_diagonal_bounds
      A B C D E F G i₀ 0 1 (by decide) hA hB hC hD hE hF hG h hstrict hA10 hB10
  have na (i j : Fin 2) : 0≤A.matrix i j := hA.1 i j
  have nb (i j : Fin 2) : 0≤B.matrix i j := hB.1 i j
  have ne (i j : Fin 2) : 0≤E.matrix i j := hE.1 i j
  have nf (i j : Fin 2) : 0≤F.matrix i j := hF.1 i j
  have ng (i j : Fin 2) : 0≤G.matrix i j := hG.1 i j
  have hE00 : E.matrix 0 0=0 := by
    have hh := h.fa.1 0 0
    change (B.matrix*E.matrix) 0 0≤(F.matrix*A.matrix) 0 0 at hh
    simp only [Matrix.mul_apply,Fin.sum_univ_two,hE10,hA10,hF00,mul_zero,zero_mul,
      add_zero] at hh
    nlinarith only [hh,hB00,ne 0 0]
  have hG00 : G.matrix 0 0=0 := by
    have hh := h.fb.1 0 0
    change (A.matrix*G.matrix) 0 0≤(F.matrix*B.matrix) 0 0 at hh
    simp only [Matrix.mul_apply,Fin.sum_univ_two,hG10,hB10,hF00,mul_zero,zero_mul,
      add_zero] at hh
    nlinarith only [hh,hA00,ng 0 0]
  have hea := h.ea.1 0 1
  have hfa := h.fa.1 0 1
  have hga := h.ga.1 0 1
  have heb := h.eb.1 0 1
  have hfb := h.fb.1 0 1
  have hgb := h.gb.1 0 1
  change (A.matrix*E.matrix) 0 1≤(E.matrix*A.matrix) 0 1 at hea
  change (B.matrix*E.matrix) 0 1≤(F.matrix*A.matrix) 0 1 at hfa
  change (A.matrix*F.matrix) 0 1≤(G.matrix*A.matrix) 0 1 at hga
  change (B.matrix*F.matrix) 0 1≤(E.matrix*B.matrix) 0 1 at heb
  change (A.matrix*G.matrix) 0 1≤(F.matrix*B.matrix) 0 1 at hfb
  change (B.matrix*G.matrix) 0 1≤(G.matrix*B.matrix) 0 1 at hgb
  simp only [Matrix.mul_apply,Fin.sum_univ_two,hE00,hF00,hG00,zero_mul,zero_add]
    at hea hfa hga heb hfb hgb
  by_cases hw : 0<F.matrix 0 1
  · have hB11 : 0<B.matrix 1 1 := by
      nlinarith only [heb,hB00,hw,ne 0 1,nb 0 1,nf 1 1]
    have hE01 : 0<E.matrix 0 1 := by
      nlinarith only [heb,hB00,hw,nb 1 1,nb 0 1,nf 1 1]
    have hA11one : 1≤A.matrix 1 1 := by
      nlinarith only [hea,hA00,hE01,na 0 1,ne 1 1]
    have hI : EntrywiseLE 1 A.matrix := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact hA00
      · exact na 0 1
      · exact na 1 0
      · exact hA11one
    have hBd : ∀ i, 0<B.matrix i i := by
      intro i
      fin_cases i
      · exact hB00
      · exact hB11
    exact strict_reversed_identity_positive_diagonals_contradiction
      A B C D E F G i₀ hA hB hC hD h hstrict hI hBd
  · have hF01 : F.matrix 0 1=0 := le_antisymm (le_of_not_gt hw) (nf 0 1)
    rw [hF01] at hfa hga heb hfb
    have hE01 : E.matrix 0 1=0 := by
      nlinarith only [hfa,hB00,ne 0 1,nb 0 1,ne 1 1]
    have hG01 : G.matrix 0 1=0 := by
      nlinarith only [hfb,hA00,ng 0 1,na 0 1,ng 1 1]
    have hne : A.matrix*B.matrix≠B.matrix*A.matrix := by
      intro hc
      apply RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions
        A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
      intro i j
      rw [hc]
    have hcross : 0<A.matrix 0 1+B.matrix 0 1 := by
      by_contra hn
      have ha : A.matrix 0 1=0 := by linarith only [hn,na 0 1,nb 0 1]
      have hb : B.matrix 0 1=0 := by linarith only [hn,na 0 1,nb 0 1]
      apply hne
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply,Fin.sum_univ_two,ha,hb,hA10,hB10,mul_comm]
    simp only [hE01,hG01,mul_zero,zero_mul,zero_add] at hga heb hfb hgb
    have hF11 : F.matrix 1 1=0 := by
      nlinarith only [hga,heb,hcross,nf 1 1,na 0 1,nb 0 1]
    have hG11 : G.matrix 1 1=0 := by
      nlinarith only [hfb,hgb,hcross,ng 1 1,na 0 1,nb 0 1]
    have hFzero : F.matrix=0 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hF00
      · exact hF01
      · exact hF10
      · exact hF11
    have hGzero : G.matrix=0 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hG00
      · exact hG01
      · exact hG10
      · exact hG11
    exact strict_reversed_zero_middle_last_contradiction
      A B C D E F G i₀ hA hB hD hE hF h hstrict hFzero hGzero

end CollatzResearch.RealTriangularZero

#print axioms CollatzResearch.RealTriangularZero.strict_upper_zero_middle_diagonal_contradiction
