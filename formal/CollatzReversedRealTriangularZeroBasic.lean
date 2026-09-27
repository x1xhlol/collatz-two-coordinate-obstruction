import CollatzReversedRealTriangularReadout

namespace CollatzResearch.RealTriangularZeroBasic

open Matrix CollatzCertificate RealAffine

set_option maxHeartbeats 1000000

theorem reversed_identity_zero_gaps
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (h : ReversedRealWeak A B C D E F G)
    (hI : EntrywiseLE 1 A.matrix) :
    D.matrix i₀ ⬝ᵥ G.offset=D.matrix i₀ ⬝ᵥ B.offset ∧
      (D.matrix i₀ ᵥ* B.matrix) ⬝ᵥ A.offset=0 := by
  let r : Vec (Fin 2) := D.matrix i₀
  have hr : 0≤r := fun i => hD.1 i₀ i
  have hq := rowMul_nonneg hr hB.1
  have hqA : r ᵥ* B.matrix≤(r ᵥ* B.matrix) ᵥ* A.matrix := by
    simpa only [Matrix.vecMul_one] using rowMul_mono_matrix hq hI
  have hdb : r ᵥ* G.matrix≤r ᵥ* B.matrix := h.db.1 i₀
  have hrow : r ᵥ* G.matrix≤r ᵥ* (B.matrix*A.matrix) := by
    simpa only [Matrix.vecMul_vecMul] using le_trans hdb hqA
  have hbg : r ⬝ᵥ G.offset≤r ⬝ᵥ B.offset := by
    have hh := h.db.2 i₀
    change r ⬝ᵥ G.offset+D.offset i₀≤r ⬝ᵥ B.offset+D.offset i₀ at hh
    linarith only [hh]
  have hgc : (B.matrix*A.matrix) *ᵥ C.offset+B.matrix *ᵥ A.offset+B.offset≤
      G.matrix *ᵥ C.offset+G.offset := by
    have hh := h.gc.2
    change B.matrix *ᵥ (A.matrix *ᵥ C.offset+A.offset)+B.offset≤
      G.matrix *ᵥ C.offset+G.offset at hh
    simpa only [Matrix.mulVec_add,Matrix.mulVec_mulVec] using hh
  have h1 := dotProduct_le_dotProduct_of_nonneg_right hrow hC.2
  have h2 := dotProduct_le_dotProduct_of_nonneg_left hgc hr
  have h3 := dotProduct_nonneg_of_nonneg hq hA.2
  simp only [dotProduct_add,dotProduct_mulVec] at h2
  change r ⬝ᵥ G.offset=r ⬝ᵥ B.offset ∧ (r ᵥ* B.matrix) ⬝ᵥ A.offset=0
  constructor <;> linarith only [h1,h2,h3,hbg]

theorem positive_diagonal_transfers_zero_readout (B : Mat (Fin 2))
    (r a : Vec (Fin 2)) (hB : EntrywiseLE 0 B) (hr : 0≤r) (ha : 0≤a)
    (hd : ∀ i, 0<B i i) (hz : (r ᵥ* B) ⬝ᵥ a=0) : r ⬝ᵥ a=0 := by
  have hq := rowMul_nonneg hr hB
  apply Finset.sum_eq_zero
  intro i hi
  have hterm : (r ᵥ* B) i*a i=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hq j) (ha j))).mp hz i hi
  have hdiag : r i*B i i≤(r ᵥ* B) i :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hr j) (hB j i)) hi
  have hmul := mul_le_mul_of_nonneg_right hdiag (ha i)
  have hprod : B i i*(r i*a i)=0 := by
    apply le_antisymm
    · nlinarith only [hmul,hterm]
    · exact mul_nonneg (hd i).le (mul_nonneg (hr i) (ha i))
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hd i))

theorem strict_reversed_identity_positive_diagonals_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hI : EntrywiseLE 1 A.matrix) (hBd : ∀ i, 0<B.matrix i i) : False := by
  obtain ⟨hbg,hqa⟩ := reversed_identity_zero_gaps A B C D E F G i₀ hA hB hC hD h hI
  have hra := positive_diagonal_transfers_zero_readout B.matrix (D.matrix i₀) A.offset
    hB.1 (fun i => hD.1 i₀ i) hA.2 hBd hqa
  rcases hstrict with hs | hs
  · change D.offset i₀<D.matrix i₀ ⬝ᵥ A.offset+D.offset i₀ at hs
    linarith only [hs,hra]
  · change D.matrix i₀ ⬝ᵥ G.offset+D.offset i₀<
      D.matrix i₀ ⬝ᵥ B.offset+D.offset i₀ at hs
    linarith only [hs,hbg]

theorem strict_reversed_zero_middle_last_contradiction
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hD : D.Nonnegative)
    (hE : E.Nonnegative) (hF : F.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hFzero : F.matrix=0) (hGzero : G.matrix=0) : False := by
  let r : Vec (Fin 2) := D.matrix i₀
  have hr : 0≤r := fun i => hD.1 i₀ i
  have hfa : B.matrix *ᵥ E.offset+B.offset≤F.offset := by
    have hh := h.fa.2
    change B.matrix *ᵥ E.offset+B.offset≤F.matrix *ᵥ A.offset+F.offset at hh
    simpa only [hFzero,Matrix.zero_mulVec,zero_add] using hh
  have hga : A.matrix *ᵥ F.offset+A.offset≤G.offset := by
    have hh := h.ga.2
    change A.matrix *ᵥ F.offset+A.offset≤G.matrix *ᵥ A.offset+G.offset at hh
    simpa only [hGzero,Matrix.zero_mulVec,zero_add] using hh
  have hbg : r ⬝ᵥ G.offset≤r ⬝ᵥ B.offset := by
    have hh := h.db.2 i₀
    change r ⬝ᵥ G.offset+D.offset i₀≤r ⬝ᵥ B.offset+D.offset i₀ at hh
    linarith only [hh]
  have h1 := dotProduct_le_dotProduct_of_nonneg_left hfa hr
  have h2 := dotProduct_le_dotProduct_of_nonneg_left hga hr
  have h3 := dotProduct_le_dotProduct_of_nonneg_right (h.da.1 i₀) hF.2
  have h4 := dotProduct_nonneg_of_nonneg (rowMul_nonneg hr hB.1) hE.2
  have h5 := dotProduct_nonneg_of_nonneg hr hA.2
  simp only [dotProduct_add,dotProduct_mulVec] at h1 h2
  change r ⬝ᵥ F.offset≤(r ᵥ* A.matrix) ⬝ᵥ F.offset at h3
  rcases hstrict with hs | hs
  · change D.offset i₀<r ⬝ᵥ A.offset+D.offset i₀ at hs
    linarith only [h1,h2,h3,h4,hbg,hs]
  · change r ⬝ᵥ G.offset+D.offset i₀<r ⬝ᵥ B.offset+D.offset i₀ at hs
    linarith only [h1,h2,h3,h4,h5,hs]

end CollatzResearch.RealTriangularZeroBasic

#print axioms CollatzResearch.RealTriangularZeroBasic.reversed_identity_zero_gaps
#print axioms CollatzResearch.RealTriangularZeroBasic.positive_diagonal_transfers_zero_readout
#print axioms CollatzResearch.RealTriangularZeroBasic.strict_reversed_identity_positive_diagonals_contradiction
#print axioms CollatzResearch.RealTriangularZeroBasic.strict_reversed_zero_middle_last_contradiction
